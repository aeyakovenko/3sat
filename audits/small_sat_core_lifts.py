"""Exact covers at eight clauses and all inclusion-minimal four-variable cores."""
from collections import defaultdict
from functools import cache
from itertools import combinations
from math import comb


def eight_clause_sets(v):
    universe = (1 << (1 << v)) - 1
    axes = [sum(1 << x for x in range(1 << v) if x >> i & 1) for i in range(v)]
    faces = []
    for support in combinations(range(v), 3):
        for signs in range(8):
            f = universe
            for i, axis in enumerate(support):
                f &= axes[axis] if signs >> i & 1 else ~axes[axis]
            faces.append(f)
    containing = [[f for f in faces if f >> x & 1] for x in range(1 << v)]

    @cache
    def cover(remaining):
        if not remaining:
            return 1
        anchor = (remaining & -remaining).bit_length() - 1
        return sum(cover(remaining ^ f) for f in containing[anchor] if remaining & f == f)
    return cover(universe)


def four_variable_cores():
    edges = [(u, u ^ (1 << j)) for u in range(16) for j in range(4) if not (u >> j & 1)]
    stars = [{} for _ in range(16)]
    for center in range(16):
        incident = [(i, v if u == center else u) for i, (u, v) in enumerate(edges)
                    if center in (u, v)]
        for k in range(1, 5):
            for branch in combinations(incident, k):
                vertices = (1 << center) + sum(1 << v for _, v in branch)
                selected = sum(1 << i for i, _ in branch)
                for v in range(16):
                    if vertices >> v & 1:
                        stars[v][selected] = vertices
    layers = defaultdict(list)

    def partition(remaining, formula):
        if not remaining:
            layers[formula.bit_count()].append(formula)
            return
        first = (remaining & -remaining).bit_length() - 1
        for selected, vertices in stars[first].items():
            if remaining & vertices == vertices:
                partition(remaining ^ vertices, formula | selected)
    partition(65535, 0)
    return layers


def trim(formula, n):
    bits = [1 << i for i in range(32) if formula >> i & 1]
    for removed in combinations(bits, n):
        yield formula - sum(removed)


def distances(parents, children):
    remaining = children
    histogram = {}
    for j in range(1, parents[0].bit_count() + 1):
        common = {f for p in parents for f in trim(p, j)}
        missed = [c for c in remaining if not any(f in common for f in trim(c, j + 1))]
        histogram[j] = len(remaining) - len(missed)
        remaining = missed
        if not remaining:
            return histogram
    raise AssertionError('every pair has the empty intersection bound')


if __name__ == '__main__':
    coefficients = []
    for v in range(8):
        coefficients.append(eight_clause_sets(v) - sum(comb(v, i) * n for i, n in enumerate(coefficients)))
    assert coefficients == [0, 0, 0, 1, 268, 3030, 7800, 5040]
    for v in (8, 9):
        assert eight_clause_sets(v) == sum(comb(v, i) * n for i, n in enumerate(coefficients))
    layers = four_variable_cores()
    counts = {k: len(v) for k, v in sorted(layers.items())}
    assert counts == {8: 272, 9: 9408, 10: 29792, 11: 10656, 12: 400}
    print('tight eight-clause coefficients', coefficients[3:])
    print('four-variable minimal cores', counts)
    for m in range(9, 13):
        hist = distances(layers[m - 1], layers[m])
        assert hist == ({1: 9024, 2: 384} if m == 9 else {1: counts[m]})
        print('child size', m, 'minimum number of deleted parent clauses', hist)
