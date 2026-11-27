"""Check image sizes, minimax scores and dense equality padding over F4."""
from fractions import Fraction
from itertools import combinations, product


def mul(a, b):
    value = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
    return value ^ (7 if value & 4 else 0)


def evaluate(word, point):
    values = [(word >> i) & 1 for i in range(1 << len(point))]
    for t in point:
        values = [a ^ mul(t, a ^ b) for a, b in zip(values[::2], values[1::2])]
    return values[0]


def span(generators):
    values = {0}
    for g in generators:
        values |= {v ^ g for v in values}
    return tuple(sorted(values))


def audit_spaces():
    n = 4
    spaces = {span(g) for size in range(n + 1) for g in combinations(range(1, 1 << n), size)}
    for space in spaces:
        for nonzero in [False, True]:
            total = hits = zeros = 0
            for p in product(range(4), repeat=2):
                image = [evaluate(w, p) for w in space]
                zeros += image.count(0)
                for key in range(int(nonzero), 4):
                    vals = [(key & z).bit_count() % 2 for z in image]
                    hits += not any(vals)
                    if any(vals):
                        assert sum(vals) * 2 == len(vals)
                    total += 1
            mu = Fraction(zeros, 16 * len(space))
            assert Fraction(hits, total) == ((4 * mu - 1) / 3 if nonzero else mu)
            assert mu <= 1 - (1 - Fraction(1, len(space))) * Fraction(3, 4)**2
    return len(spaces)


def audit_padded():
    tested = 0
    for word in range(16):
        copies = word | (word << 12)
        for p in product(range(4), repeat=2):
            for a, b in product(range(4), repeat=2):
                assert evaluate(copies, (*p, a, b)) == mul(evaluate(word, p), 1 ^ a ^ b)
                tested += 1
    return tested


if __name__ == "__main__":
    print(f"{audit_spaces()} complete affine direction spaces checked on both mask distributions")
    print(f"{audit_padded():,} equality-padded evaluations checked")
