"""Exhaust the four-vertex complete graph and check the comparison Fourier expansion."""

from cmath import exp
from itertools import combinations, permutations, product
from math import log, pi


def component(edges, source):
    reached = {source}
    for _ in range(3):
        for u, v in edges:
            if u in reached or v in reached:
                reached.update((u, v))
    return reached


def replacement_groups(edges, tree):
    groups = []
    for edge_id in tree:
        u, _ = edges[edge_id]
        cut = component([edges[f] for f in tree if f != edge_id], u)
        by_owner = [[], [], []]
        for f, (a, b) in enumerate(edges):
            if f not in tree and (a in cut) != (b in cut):
                by_owner[f % 3].append(f)
        groups.extend((edge_id, group) for group in by_owner if group)
    return groups


def audit_forests():
    edges = list(combinations(range(4), 2))
    trees = [tree for tree in combinations(range(6), 3)
             if len(component([edges[f] for f in tree], 0)) == 4]
    assert len(trees) == 16
    checks = {tree: replacement_groups(edges, tree) for tree in trees}
    for weights in permutations(range(6)):
        accepted = [tree for tree in trees
                    if all(weights[e] < min(weights[f] for f in group)
                           for e, group in checks[tree])]
        optimum = min(sum(weights[f] for f in tree) for tree in trees)
        assert accepted == [tree for tree in trees if sum(weights[f] for f in tree) == optimum]
    for tree in trees:
        weights = [f if f in tree else f + len(edges) for f in range(len(edges))]
        assert all(weights[e] < min(weights[f] for f in group) for e, group in checks[tree])
    return len(trees) * 720


def audit_fourier():
    count = 0
    for q in (2, 4, 8, 16, 32):
        periods = [exp(2j * pi * j / (2 * q)) for j in range(2 * q)]
        coefficients = [sum(root ** (-t) for t in range(1, q)) / (2 * q)
                        for root in periods]
        assert sum(map(abs, coefficients)) < 2 + log(2 * q)
        for x, y in product(range(q), repeat=2):
            reconstructed = sum(coef * root ** (y - x)
                                for root, coef in zip(periods, coefficients))
            assert abs(reconstructed - (x < y)) < 1e-10
            count += 1
    return count


if __name__ == "__main__":
    print(f"{audit_forests()} minimum tree certificates and {audit_fourier()} ordered-key comparisons passed")
