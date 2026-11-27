"""Check adaptive discovery cuts on the extended binary Golay code."""
from collections import Counter
from itertools import combinations


def extended_code():
    # Cyclic length-23 generator with degree 11, followed by overall parity.
    generator = sum(1 << i for i in (0, 1, 5, 6, 7, 9, 11))
    words = {0}
    for i in range(12):
        words.update([w ^ (generator << i) for w in words])
    words = {w | ((w.bit_count() % 2) << 23) for w in words}
    assert len(words) == 4096 and min(w.bit_count() for w in words if w) == 8
    generators = [(generator << i) | (1 << 23) for i in range(12)]
    assert all((v & w).bit_count() % 2 == 0 for v in generators for w in words)
    return words  # Self-orthogonality and dimension 12 imply self-duality.


def history(word, depth):
    used, answer, value = {}, 0, 0
    for step in range(depth):
        # The next unseen address depends on earlier answers.
        address = (5 * step + 3 * answer) % 24
        while address in used:
            address = (address + 1) % 24
        value = (word >> address) & 1
        used[address] = value
        answer = 2 * answer + value
    return tuple(used.items())


def check_cuts():
    code = extended_code()
    tested_pairs = 0
    for depth in (1, 2, 3):
        groups = Counter(history(word, depth) for word in code)
        assert len(groups) == 2**depth and set(groups.values()) == {4096 >> depth}
        # A solver can throw away its whole prefix and check membership afresh.
        # Then every prefix is merged at one state. For each merge, enumerate
        # the exact affine fiber and the changes a correct suffix must detect.
        for first, second in combinations(groups, 2):
            p, q = dict(first), dict(second)
            differences = sum(1 << i for i in p.keys() & q.keys() if p[i] != q[i])
            assert 0 < differences.bit_count() <= depth
            priority = {**q, **p}
            prescribed = sum(v << i for i, v in priority.items())
            mask = sum(1 << i for i in priority)
            fiber = [word for word in code if word & mask == prescribed]
            assert len(fiber) == 4096 >> len(priority)
            for word in fiber:
                alternate = word ^ differences
                assert history(word, depth) == first
                assert history(alternate, depth) == second and alternate not in code
            tested_pairs += 1
    return tested_pairs


if __name__ == "__main__":
    print(f"{check_cuts()} adaptive merge pairs checked on the 4096-word code")
