"""Integer uncrossing of bit-wire permutations on alternating boundary ports."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations, product
from math import comb


def wire_matching(p):
    return tuple(sorted(tuple(sorted((2*i, 2*j+1))) for i, j in enumerate(p)))


def crossing(edges):
    return next(((i, k, j, l) for (i, k), (j, l) in combinations(edges, 2)
                 if i < j < k < l), None)


@cache
def straighten(edges):
    cross = crossing(edges)
    if cross is None:
        return {edges: 1}
    i, k, j, l = cross
    rest = set(edges) - {(i, k), (j, l)}
    expansion = Counter()
    for replacement in (((i, j), (k, l)), ((i, l), (j, k))):
        child = tuple(sorted(rest.union(replacement)))
        expansion.update(straighten(child))
    return dict(expansion)


def orientation(edges):
    return (-1)**sum(i % 2 for i, _ in edges)


def equality_expansion(p):
    edges = wire_matching(p)
    return {leaf: orientation(edges)*orientation(leaf)*value
            for leaf, value in straighten(edges).items()}


def agrees(colors, edges):
    return all(colors[i] == colors[j] for i, j in edges)


def leading_word(edges):
    opens = {i for i, _ in edges}
    return tuple(int(i not in opens) for i in range(2*len(edges)))


def dual_degree(edges):
    # After an opener, the tour enters a fresh face whose parent edge is
    # the opened chord. The outer face is numbered zero.
    opens = {i for i, _ in edges}
    degrees = [0]
    stack = [0]
    for endpoint in range(2*len(edges)):
        if endpoint in opens:
            degrees[stack[-1]] += 1
            stack.append(len(degrees))
            degrees.append(1)
        else:
            stack.pop()
    return max(degrees)


def can_isolate(edges, others, q):
    for edge_colors in product(range(q), repeat=len(edges)):
        colors = [0] * (2*len(edges))
        for (i, j), c in zip(edges, edge_colors):
            colors[i] = colors[j] = c
        if all(not agrees(colors, other) for other in others):
            return True
    return False


def check_all(m):
    cases = rows = separators = 0
    bits = list(product(range(2), repeat=2*m))
    ps = list(permutations(range(m)))
    matchings = [wire_matching(p) for p in ps]
    planar = [edges for edges in matchings if not crossing(edges)]
    assert len(set(map(leading_word, planar))) == len(planar) == comb(2*m, m)//(m+1)
    binary_exposed = []
    for edges in planar:
        others = [other for other in planar if other != edges]
        degree = dual_degree(edges)
        assert can_isolate(edges, others, degree)
        if degree > 1:
            assert not can_isolate(edges, others, degree-1)
        if degree <= 2:
            binary_exposed.append(leading_word(edges))
    assert set(binary_exposed) == {(0,)*k + (1,)*k + (0,)*(m-k) + (1,)*(m-k)
                                    for k in range(m)}
    for p, edges in zip(ps, matchings):
        coeffs = equality_expansion(p)
        assert set(coeffs) <= set(planar)
        for colors in bits:
            expected = agrees(colors, edges)
            actual = sum(c for leaf, c in coeffs.items() if agrees(colors, leaf))
            assert actual == expected
            rows += 1
        if cross := crossing(edges):
            i, k, j, l = cross
            colors = [0] * (2*m)
            colors[i] = colors[k] = 1
            colors[j] = colors[l] = 2
            assert agrees(colors, edges)
            assert all(not agrees(colors, leaf) for leaf in planar)
            separators += 1
        cases += 1
    return cases, rows, separators


def check_crossing_triples(r):
    perm = tuple(3*i+j for i in range(r) for j in (1, 2, 0))
    coeffs = equality_expansion(perm)
    assert len(coeffs) == 5**r
    assert all(abs(value) == 1 for value in coeffs.values())


if __name__ == '__main__':
    totals = [sum(x) for x in zip(*(check_all(m) for m in range(1, 6)))]
    print('permutations, integer truth-table entries, ternary separators:', *totals)
    for r in range(1, 5):
        check_crossing_triples(r)
    print('triple-product support sizes:', *(5**r for r in range(1, 5)))
