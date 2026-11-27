"""Audit successive minimum spanning forests and affine reads on the clique scaffold."""

from functools import cache
from itertools import combinations, product

from unit_sat_list_transfer_audit import duplicate_cnf


def edge(a, b):
    return (a, b) if a < b else (b, a)


def walecki_path(k, j):
    vertices = [j]
    for offset in range(1, k):
        vertices.extend([(j - offset) % (2 * k), (j + offset) % (2 * k)])
    vertices.append((j - k) % (2 * k))
    assert sorted(vertices) == list(range(2 * k))
    return vertices


def scaffold(q, k, data_edges):
    width = 2 * k + 2
    n = q * width
    weights = {}
    trees = []
    for j in range(k):
        tree = set()
        path = walecki_path(k, j)
        for i in range(q):
            start = i * width
            a = start + j
            b = start + k + j
            filler = start + 2 * k
            data = filler + 1
            tree.update(edge(start + u, start + v) for u, v in zip(path, path[1:]))
            tree.update([edge(filler, a), edge(data, a)])
            if i + 1 < q:
                tree.add(edge(b, a + width))
        assert len(tree) == n - 1 and tree.isdisjoint(weights)
        weights.update((e, j + 1) for e in tree)
        trees.append(tree)
    for i in range(q):
        start = i * width
        for u, v in combinations(range(2 * k + 1), 2):
            weights.setdefault(edge(start + u, start + v), k + 1)
    for u, v in data_edges:
        e = edge((u + 1) * width - 1, (v + 1) * width - 1)
        assert e not in weights
        weights[e] = k + 2
    return n, weights, trees


def kruskal(n, weights, available):
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    forest = set()
    for u, v in sorted(available, key=lambda e: (weights[e], e)):
        a, b = root(u), root(v)
        if a != b:
            parent[a] = b
            forest.add((u, v))
    return forest


def check_prefixes(n, weights, trees):
    for cutoff in range(len(trees) + 3):
        remaining = {e for e, w in weights.items() if w <= cutoff}
        for tree in trees:
            forest = kruskal(n, weights, remaining)
            assert forest == {e for e in tree if weights[e] <= cutoff}
            remaining.difference_update(forest)


def independent_number(n, edges):
    neighbors = [0] * n
    for u, v in edges:
        neighbors[u] |= 1 << v
        neighbors[v] |= 1 << u

    @cache
    def largest(vertices):
        if not vertices:
            return 0
        v = max(
            (i for i in range(n) if vertices >> i & 1),
            key=lambda i: (neighbors[i] & vertices).bit_count(),
        )
        rest = vertices ^ (1 << v)
        return max(largest(rest), 1 + largest(rest & ~neighbors[v]))

    return largest((1 << n) - 1)


def affine_on_span(truth, basis):
    # A zero-centered linear form is determined by its values on the basis.
    points = [0]
    for vector in basis:
        other = [x ^ vector for x in points]
        for x, y in zip(points, other):
            if truth[y] != (truth[x] ^ truth[vector]):
                return False
        points += other
    return True


def echelon_bases(n, d):
    for pivots in combinations(range(n), d):
        choices = []
        for pivot in pivots:
            rows = [1 << pivot]
            for col in range(pivot + 1, n):
                if col not in pivots:
                    rows += [x | (1 << col) for x in rows]
            choices.append(rows)
        yield from product(*choices)


def check_affine(n, edges, dimension):
    masks = [(1 << u) | (1 << v) for u, v in edges]
    truth = [any(x & e == e for e in masks) for x in range(1 << n)]
    assert any(affine_on_span(truth, b) for b in echelon_bases(n, dimension))
    # Any still larger affine restriction contains a subspace of this dimension.
    assert not any(
        affine_on_span(truth, b) for b in echelon_bases(n, dimension + 1)
    )


def cubic_profiles():
    q = 6
    cycle = {edge(i, (i + 1) % q) for i in range(q)}
    prism = cycle | {(0, 2), (1, 4), (3, 5)}
    bipartite = cycle | {(0, 3), (1, 4), (2, 5)}
    assert independent_number(q, prism) == 2
    assert independent_number(q, bipartite) == 3
    for k in range(1, 5):
        profiles = []
        tree_lists = []
        for graph in [prism, bipartite]:
            n, weights, trees = scaffold(q, k, graph)
            check_prefixes(n, weights, trees)
            profile = []
            for cutoff in range(k + 3):
                degrees = [0] * n
                for (u, v), w in weights.items():
                    if w <= cutoff:
                        degrees[u] += 1
                        degrees[v] += 1
                profile.append(degrees)
            assert max(profile[-1]) <= 2 * k + 2
            profiles.append(profile)
            tree_lists.append(trees)
        assert profiles[0] == profiles[1] and tree_lists[0] == tree_lists[1]


def duplicate_graph_threshold(records):
    # A group represents a clique. A maximum independent transversal takes
    # exactly one member per group. Repeated literals are interchangeable.
    clauses, first_unused, _ = duplicate_cnf(records)
    num_vars = first_unused - 1
    groups = [{2 * i, 2 * i + 1} for i in range(num_vars)]
    neighbors = {v: set() for g in groups for v in g}
    vertex = 2 * num_vars
    for clause in clauses:
        group = set()
        for lit in clause:
            opposite = 2 * (abs(lit) - 1) + int(lit < 0)
            neighbors[vertex] = {opposite}
            neighbors[opposite].add(vertex)
            group.add(vertex)
            vertex += 1
        groups.append(group)

    def can_complete(remaining):
        if not remaining:
            return True
        pivot = min(range(len(remaining)), key=lambda i: len(remaining[i]))
        others = remaining[:pivot] + remaining[pivot + 1:]
        for chosen in remaining[pivot]:
            if can_complete([g - neighbors[chosen] for g in others]):
                return True
        return False

    return can_complete(groups)


def audit_duplicate_threshold():
    cases = list(product(range(4), repeat=2))
    for records in cases:
        assert duplicate_graph_threshold(records) == (len(set(records)) < len(records))
    return len(cases)


def main():
    graph_cases = affine_cases = 0
    for q in range(1, 5):
        pairs = list(combinations(range(q), 2))
        for mask in range(1 << len(pairs)):
            graph = [e for i, e in enumerate(pairs) if mask >> i & 1]
            alpha = independent_number(q, graph)
            for k in range(1, 4):
                n, weights, trees = scaffold(q, k, graph)
                check_prefixes(n, weights, trees)
                assert independent_number(n, weights) == q + alpha
                graph_cases += 1
                if n <= 8:
                    check_affine(n, weights, q + alpha + 1)
                    affine_cases += 1
    cubic_profiles()
    print(f"{audit_duplicate_threshold()} two-record lists checked by graph transversal search")
    print(f"{graph_cases} graph/scaffold pairs passed all prefix and independence tests")
    print(f"{affine_cases} centered affine dimensions checked by enumerating finite flats")
    print("Two cubic data graphs matched every labeled threshold degree and forest for k=1..4")


if __name__ == "__main__":
    main()
