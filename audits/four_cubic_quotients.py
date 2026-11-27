"""All possible pure-component quotients of a four-site cubic obstruction."""
from itertools import combinations, permutations, product

SITES = range(4)
PAIRS = list(combinations(SITES, 2))


def canonical(edges, n):
    images = []
    for marked in permutations(SITES):
        for pure in permutations(range(4, n)):
            p = marked + pure
            images.append(tuple(sorted(tuple(sorted((p[u], p[v]))) for u, v in edges)))
    return min(images)


def connected_after_deletion(edges, n, removed):
    vertices = set(range(n)) - set(removed)
    seen = {min(vertices)}
    while True:
        new = seen | {v for edge in edges if seen.intersection(edge)
                      for v in edge if v in vertices}
        if new == seen:
            return seen == vertices
        seen = new


def quotient_types():
    types = set()
    for mask in range(1 << len(PAIRS)):
        internal = [e for j, e in enumerate(PAIRS) if mask >> j & 1]
        degrees = [sum(v in e for e in internal) for v in SITES]
        if min(degrees) == 0:
            continue
        stubs = [v for v in SITES for _ in range(3 - degrees[v])]
        for components in range(len(stubs) // 3 + 1):
            pure = range(4, 4 + components)
            for placement in product(pure, repeat=len(stubs)):
                boundary = list(zip(stubs, placement))
                if any(len({v for v, p in boundary if p == i}) < 3 for i in pure):
                    continue
                edges = internal + boundary
                if all(connected_after_deletion(edges, 4 + components, pair) for pair in PAIRS):
                    types.add(canonical(edges, 4 + components))
    return sorted(types)


def unsat_edits(edges):
    n = 1 + max(v for edge in edges for v in edge)
    incident = [[i for i, edge in enumerate(edges) if v in edge] for v in range(n)]
    assert all(len(incident[v]) == 3 for v in SITES)

    def pattern(x, v):
        return sum((x >> i & 1) << j for j, i in enumerate(incident[v]))

    feasible = 0
    masks = [[0] * 8 for _ in SITES]
    for x in range(1 << len(edges)):
        if any(pattern(x, v).bit_count() % 2 for v in range(4, n)):
            continue
        feasible |= 1 << x
        for v in SITES:
            masks[v][pattern(x, v)] |= 1 << x

    options = []
    for v in SITES:
        bad = [p for p in range(8) if p.bit_count() % 2 != int(v == 0)]
        original = feasible ^ sum(masks[v][p] for p in bad)
        options.append([(original | masks[v][b]) & ~masks[v][b ^ (1 << i)]
                        for b in bad for i in range(3)])
    return sum(not (a & b & c & d) for a, b, c, d in product(*options))


def main():
    types = quotient_types()
    counts = [0] * 3
    for edges in types:
        components = 1 + max(v for edge in edges for v in edge) - 4
        counts[components] += 1
        failing = unsat_edits(edges)
        assert failing == (96 if components == 0 else 0)
        print(edges, failing)
    assert counts == [1, 5, 5]
    print("Quotients by number of pure components:", counts)


if __name__ == "__main__":
    main()
