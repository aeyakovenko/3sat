"""Check descending XOR derivations by enumeration on four named vertices."""

from itertools import combinations, product


def walks_to_sinks_and_ancestors(edges):
    ancestors = []
    for v, outgoing in enumerate(edges):
        values = {(v, 0)}
        for u, label in outgoing:
            values.update((target, label ^ bit) for target, bit in ancestors[u])
        ancestors.append(values)
    return ancestors


def compatible_forks(edges, ancestors):
    for outgoing in edges:
        continuations = [
            {(target, label ^ bit) for target, bit in ancestors[u]} for u, label in outgoing
        ]
        if any(left.isdisjoint(right) for left, right in combinations(continuations, 2)):
            return False
    return True


def has_potential(edges):
    return any(all((bits[v] ^ bits[u]) == label for v, children in enumerate(edges)
                   for u, label in children) for bits in product((0, 1), repeat=len(edges)))


def check_graphs(n):
    keys = [(v, u) for v in range(n) for u in range(v)]
    joined = one_sink = 0
    for options in product(range(4), repeat=len(keys)):
        edges = [[] for _ in range(n)]
        for (v, u), mask in zip(keys, options):
            edges[v].extend((u, bit) for bit in (0, 1) if (mask >> bit) & 1)
        accepted = compatible_forks(edges, walks_to_sinks_and_ancestors(edges))
        has_solution = has_potential(edges)
        assert not accepted or has_solution
        if sum(not outgoing for outgoing in edges) == 1:
            assert accepted == has_solution
            one_sink += 1
        joined += accepted
    print(f'{4 ** len(keys)} graphs; {joined} have compatible forks; {one_sink} have a single sink')


def check_anchor():
    for triple in product((0, 1), repeat=3):
        first, second, third = triple
        options = []
        for y in (0, 1):
            contexts = [(first, second, y), (1 ^ y, third, 0)]
            if any(min(c) == max(c) for c in contexts):
                continue
            options.extend(int(2 in pair) for pair in combinations(range(3), 2)
                           if contexts[1][pair[0]] != contexts[1][pair[1]])
        assert bool(options) == bool(any(triple))
        if options:
            assert min(options) == all(triple)
    print('All 8 clause patterns meet the anchor-use criterion')


if __name__ == '__main__':
    check_graphs(4)
    check_anchor()
