"""Exact Walsh maxima on one and two CCZ blocks, and a mixed-affine cubic identity."""

from itertools import combinations, product
from random import Random


def sign(value):
    return 1 - 2 * value


def binary_parity(x):
    return x.bit_count() % 2


def walsh(values):
    transformed = values[:]
    span = 1
    while span < len(transformed):
        for base in range(0, len(transformed), 2 * span):
            for left in range(base, base + span):
                a, b = transformed[left], transformed[left + span]
                transformed[left], transformed[left + span] = a + b, a - b
        span *= 2
    return transformed


def quad_phase_max(variables):
    assignments = range(1 << variables)
    pair_signs = []
    for i, j in combinations(range(variables), 2):
        mask = (1 << i) | (1 << j)
        pair_signs.append([x for x in assignments if x & mask == mask])
    values = [sign(sum((x >> j) & 7 == 7 for j in range(0, variables, 3)) % 2)
              for x in assignments]
    best = max(map(abs, walsh(values)))
    # Gray code toggles one pair term at a time. The Walsh transform enumerates
    # every possible additional linear form, and a constant only changes sign.
    for counter in range(1, 1 << len(pair_signs)):
        index = (counter & -counter).bit_length() - 1
        for x in pair_signs[index]:
            values[x] *= -1
        best = max(best, max(map(abs, walsh(values))))
    return best


def audit_translation():
    for y in range(8):
        assert sum(sign((y == 7) ^ ((y ^ u) == 7)) for u in range(8)) == 6 * sign(y == 7)
    rng = Random(1206)
    for _ in range(256):
        a, b, c = [rng.randrange(128) for _ in range(3)]
        # Bit six is the affine offset; the remaining bits use all six source coordinates.
        for choice in range(64):
            lifted = choice | 64
            y = sum(binary_parity(lifted & mask) << j for j, mask in enumerate((a, b, c)))
            assert sum(sign((y == 7) ^ ((y ^ u) == 7)) for u in range(8)) == 6 * sign(y == 7)


def audit_scanner():
    for rows in product(range(8), repeat=3):
        acc = 0
        for a in rows:
            acc ^= ((a >> 2) & (a >> 1) & a) & 1
        assert acc == sum(x == 7 for x in rows) % 2
    rng = Random(301)
    for h in range(1, 16):
        for _ in range(32):
            acc = total = 0
            for _ in range(25):
                a, b, z = (rng.getrandbits(h) for _ in range(3))
                acc ^= a & b & z
                total += binary_parity(a & b & z)
            assert binary_parity(acc) == total % 2


if __name__ == "__main__":
    assert quad_phase_max(3) == 6
    assert quad_phase_max(6) == 36
    audit_translation()
    audit_scanner()
    print("All 4194304 two-block quadratic phases (including constants), translated cubic identities and public-index parity evaluations passed")
