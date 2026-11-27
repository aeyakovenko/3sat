"""Exact checks of ternary Walsh signs, fixed-coordinate quotients and buried pins."""

from random import Random

from modular_noisy_gate_evaluation_audit import gates, logical_output, physical_output


def walsh_numerators(signs):
    result = signs.copy()
    span = 1
    while span < len(result):
        for offset in range(0, len(result), 2 * span):
            for i in range(offset, offset + span):
                x, y = result[i], result[i + span]
                result[i], result[i + span] = x + y, x - y
        span *= 2
    return result


def residues(coefficients):
    inverse = pow(len(coefficients), -1, 3)
    return [c * inverse % 3 for c in coefficients]


def square_power_audit():
    for seed in range(96):
        circuit = gates(seed)
        m = len(circuit)
        signs = [1 - 2 * logical_output(circuit, r) for r in range(1 << m)]
        coefficients = walsh_numerators(signs)
        assert all(not c or abs(c).bit_count() == 1 for c in coefficients)
        ternary = residues(coefficients)
        assert (len(ternary) - ternary.count(0)) % 3 == 1
        for r, sign in enumerate(signs):
            mistakes = sum(
                c != 0 and c != (-1 if (s & r).bit_count() % 2 else 1) % 3
                for s, c in enumerate(ternary)
            )
            assert mistakes % 3 == (1 - sign) // 2
        physical = walsh_numerators([
            1 - 2 * physical_output(circuit, r) for r in range(1 << (2 * m))
        ])
        for support, value in enumerate(physical):
            pairs = [(support >> (2 * i)) & 3 for i in range(m)]
            if any(pair in (1, 2) for pair in pairs):
                assert value == 0
            else:
                logical = sum((p == 3) << i for i, p in enumerate(pairs))
                assert value == (1 << m) * coefficients[logical]


def permute_mask(mask, perm):
    return sum(((mask >> i) & 1) << j for i, j in enumerate(perm))


def orbits(size, generators):
    unused = set(range(size))
    result = []
    while unused:
        start = min(unused)
        orbit, todo = {start}, [start]
        while todo:
            x = todo.pop()
            for gen in generators:
                y = gen(x)
                if y not in orbit:
                    orbit.add(y)
                    todo.append(y)
        unused.difference_update(orbit)
        result.append(sorted(orbit))
    return result


def quotient_audit():
    rng = Random(128)
    tested = 0
    for perms in (
        [[1, 2, 0, 3]],
        [[1, 2, 0, 3, 4, 5], [0, 1, 2, 4, 5, 3]],
        [[1, 2, 3, 4, 5, 6, 7, 8, 0]],
    ):
        m = len(perms[0])
        coords = orbits(m, [lambda i, p=p: p[i] for p in perms])
        inputs = orbits(1 << m, [lambda x, p=p: permute_mask(x, p) for p in perms])
        repeated = [
            sum(1 << i for j, orbit in enumerate(coords) if (x >> j) & 1 for i in orbit)
            for x in range(1 << len(coords))
        ]
        all_functions = len(inputs) <= 8
        for case in range((1 << len(inputs)) if all_functions else 100):
            word = case if all_functions else rng.getrandbits(len(inputs))
            signs = [0] * (1 << m)
            for j, orbit in enumerate(inputs):
                for x in orbit:
                    signs[x] = 1 - 2 * ((word >> j) & 1)
            original = residues(walsh_numerators(signs))
            restricted = residues(walsh_numerators([signs[x] for x in repeated]))
            assert [original[x] for x in repeated] == restricted
            assert all(original.count(c) % 3 == restricted.count(c) % 3 for c in (1, 2))
            tested += 1
    return tested


def flag_sign(r, length, pin, core):
    native = core ^ (r & 1)
    flag = pin ^ (r >> 1 & 1)
    for i in range(length):
        sibling = 1 ^ (r >> (2 + 2 * i) & 1)
        flag = (flag & sibling) ^ (r >> (3 + 2 * i) & 1)
    return 1 - 2 * (native ^ flag ^ (r >> (2 + 2 * length) & 1))


def flag_audit():
    for length in range(1, 6):
        m = 3 + 2 * length
        size = 1 << m
        for core in (0, 1):
            left, right = [
                [flag_sign(r, length, pin, core) for r in range(size)] for pin in (0, 1)
            ]
            assert sum(a != b for a, b in zip(left, right)) * (1 << length) == size
            xs, ys = map(walsh_numerators, (left, right))
            assert all(b == (-a if s & 2 else a) for s, (a, b) in enumerate(zip(xs, ys)))
            assert all(a == b for s, (a, b) in enumerate(zip(xs, ys))
                       if s.bit_count() <= length + 1)
            assert sum((a - b) ** 2 for a, b in zip(xs, ys)) * (1 << length) == 4 * size**2
            assert sum(a != b for a, b in zip(xs, ys)) % 3 == (-1) ** length % 3
            assert residues(xs).count(2) % 3 == core
            assert residues(ys).count(2) % 3 == 1 - core


def adaptive_tree_audit():
    leaves = 4
    size = 1 << 9

    def tree_sign(r, hidden):
        values = [(i != hidden) ^ ((r >> i) & 1) for i in range(leaves)]
        for i in range(3):
            values.append((values[2 * i] & values[2 * i + 1]) ^ ((r >> (4 + i)) & 1))
        answer = values[-1] ^ ((r >> 7) & 1) ^ ((r >> 8) & 1)
        return 1 - 2 * answer

    spectra = [
        walsh_numerators([tree_sign(r, hidden) for r in range(size)])
        for hidden in range(-1, leaves)
    ]
    rng = Random(42)
    for _ in range(128):
        first = rng.randrange(size)
        followups = [rng.randrange(size) for _ in range(3)]

        def read(spectrum):
            second = followups[(spectrum[first] > 0) - (spectrum[first] < 0) + 1]
            return (spectrum[first], spectrum[second]), second

        reference, second = read(spectra[0])
        mentioned = (first | second) & ((1 << leaves) - 1)
        distinguished = [read(spectrum)[0] != reference for spectrum in spectra[1:]]
        assert all(not different or mentioned >> i & 1 for i, different in enumerate(distinguished))


if __name__ == "__main__":
    square_power_audit()
    quotients = quotient_audit()
    flag_audit()
    adaptive_tree_audit()
    print(f"96 buffered spectra, {quotients} invariant functions, 10 nonlinear flag pairs, "
          "128 adaptive tree queries")
