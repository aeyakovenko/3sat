"""Finite tests of interpolation and binary coefficient recovery over prime fields."""

from collections import Counter
from math import comb
from random import Random


def word_graph(word, length, prime):
    """Bit i is the coefficient of X^i, including high zero coefficients."""
    for x in range(prime):
        value = sum(((word >> i) & 1) * pow(x, i, prime) for i in range(length))
        yield x, value % prime


def interpolate(marks, length, prime):
    """Find a nonzero homogeneous solution in the manuscript's monomial box."""
    monomials = [
        (u, v)
        for u in range(prime // 2)
        for v in range(prime // (2 * (length + 1)) + 1)
    ]
    monomials.sort(key=lambda uv: (uv[0] + (length - 1) * uv[1], uv[1]))
    assert len(monomials) > len(marks)
    assert max(u + (length - 1) * v for u, v in monomials) < prime
    rows = [
        [pow(x, u, prime) * pow(y, v, prime) % prime for u, v in monomials]
        for x, y in sorted(marks)
    ]
    pivots = []
    for column in range(len(monomials)):
        rank = len(pivots)
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            # The first dependent column already gives a null vector.
            break
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        basis = rows[rank]
        inverse = pow(basis[column], -1, prime)
        for i in range(rank + 1, len(rows)):
            factor = rows[i][column] * inverse % prime
            if factor:
                rows[i] = [(a - factor * b) % prime for a, b in zip(rows[i], basis)]
        pivots.append(column)
    coefficients = [0] * len(monomials)
    coefficients[column] = 1
    for i in reversed(range(len(pivots))):
        pivot = pivots[i]
        total = sum(a * b for a, b in zip(rows[i], coefficients))
        coefficients[pivot] = -total * pow(rows[i][pivot], -1, prime) % prime
    poly = {uv: c for uv, c in zip(monomials, coefficients) if c}
    for x, y in marks:
        assert sum(c * pow(x, u, prime) * pow(y, v, prime) for (u, v), c in poly.items()) % prime == 0
    return poly


def normalize(poly, prime):
    poly = {uv: c % prime for uv, c in poly.items() if c % prime}
    offset = min(u for u, _ in poly)
    return {(u - offset, v): c for (u, v), c in poly.items()}


def shift(poly, bit, prime):
    """Substitute Y = bit + X*Y and remove the common power of X."""
    result = Counter()
    for (u, v), c in poly.items():
        if bit == 0:
            result[u + v, v] += c
        else:
            for k in range(v + 1):
                result[u + k, k] += c * comb(v, k)
    return normalize(result, prime)


def extract(poly, length, prime, stats):
    poly = normalize(poly, prime)
    degree_bound = max(v for _, v in poly)
    level = [(0, poly)]
    for i in range(length):
        children = []
        for prefix, current in level:
            h = {v: c for (u, v), c in current.items() if u == 0}
            child_total = 0
            for bit in (0, 1):
                # The first nonzero coefficient of h(bit + Z) is the multiplicity.
                multiplicity = next(
                    k for k in range(max(h) + 1)
                    if sum(c * comb(v, k) * bit ** (v - k)
                           for v, c in h.items() if v >= k) % prime
                )
                if multiplicity == 0:
                    continue
                child = shift(current, bit, prime)
                child_degree = max(v for u, v in child if u == 0)
                assert child_degree <= multiplicity
                stats["repeated"] += multiplicity > 1
                stats["zero_budget"] += child_degree == 0
                child_total += child_degree
                children.append((prefix | (bit << i), child))
            assert child_total <= max(h)
        assert len(children) <= degree_bound
        level = children
    return {word for word, _ in level}


def check(marks, length, prime, stats):
    expected = {word for word in range(1 << length) if marks.issuperset(word_graph(word, length, prime))}
    poly = interpolate(marks, length, prime)
    # Squaring preserves polynomial roots, forces multiplicities, and a common
    # factor X^3 also exercises normalization at the root of the search tree.
    square = Counter()
    for (u, v), a in poly.items():
        for (s, t), b in poly.items():
            square[u + s + 3, v + t] += a * b
    for interpolant in (poly, square):
        leaves = extract(interpolant, length, prime, stats)
        actual = {word for word in leaves if marks.issuperset(word_graph(word, length, prime))}
        assert expected == actual, (length, prime, expected, actual)
        stats["filtered"] += len(leaves - actual)
    stats["tables"] += 1
    stats["words"] += 1 << length
    stats["solutions"] += len(expected)
    return expected


def main():
    stats = Counter()
    for words in ((), (0,), (5, 13)):
        marks = {cell for word in words for cell in word_graph(word, 4, 47)}
        assert check(marks, 4, 47, stats) == set(words)
    # A graph missing one cell passes interpolation but fails the final check.
    partial = set(word_graph(3, 4, 47))
    partial.remove((0, 1))
    assert check(partial, 4, 47, stats) == set()
    assert stats["filtered"] > 0
    # Y^2-X starts with a double root and gives a normalized constant slice -1.
    assert not extract({(0, 2): 1, (1, 0): -1}, 3, 37, stats)
    assert stats["zero_budget"] > 0 and stats["repeated"] > 0

    rng = Random(249)
    for length, prime in ((2, 31), (3, 37), (4, 47), (5, 59)):
        for trial in range(6):
            planted = rng.sample(range(1 << length), trial % 3)
            marks = {cell for word in planted for cell in word_graph(word, length, prime)}
            marks.update((rng.randrange(prime), rng.randrange(prime)) for _ in range(8))
            assert set(planted) <= check(marks, length, prime, stats)
    print(f"{stats['tables']} tables (4 fixed, 24 seeded), {stats['words']} exhaustive words, "
          f"{stats['solutions']} fully marked words")
    print(f"interpolant and squared interpolant agree with exhaustive search; "
          f"{stats['repeated']} repeated-root edges, {stats['filtered']} leaves discarded")


if __name__ == "__main__":
    main()
