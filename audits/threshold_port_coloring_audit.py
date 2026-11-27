"""Finite checks of equality paths, their quotient coloring, and threshold births."""

from collections import Counter
from itertools import combinations, product
from random import Random


class Components:
    def __init__(self, size):
        self.parent = list(range(size))

    def root(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def join(self, u, v):
        self.parent[self.root(u)] = self.root(v)


def make_paths(order, edges):
    """One oriented variable per edge. Return rows and the vertex of each port."""
    degrees = Counter(v for edge in edges for v in edge)
    work = list(edges)
    odd = [v for v in range(order) if degrees[v] % 2]
    work.extend((v, order) for v in odd)
    incidence = [[] for _ in range(order + 1)]
    for idx, (u, v) in enumerate(work):
        incidence[u].append((idx, v))
        incidence[v].append((idx, u))
    seen = set()
    endpoint = [None] * (2 * len(edges))
    for start in range(order + 1):
        stack = [start]
        while stack:
            u = stack[-1]
            if not incidence[u]:
                stack.pop()
                continue
            idx, v = incidence[u].pop()
            if idx in seen:
                continue
            seen.add(idx)
            if idx < len(edges):
                endpoint[2*idx:2*idx+2] = [u, v]
            stack.append(v)

    groups = [[[], []] for _ in range(order)]
    for port, v in enumerate(endpoint):
        groups[v][port % 2].append(port)
    rows = []
    for tails, heads in groups:
        assert abs(len(tails) - len(heads)) <= 1
        first, second = (tails, heads) if len(tails) >= len(heads) else (heads, tails)
        path = [first[i//2] if i % 2 == 0 else second[i//2]
                for i in range(len(tails) + len(heads))]
        for a, b in zip(path, path[1:]):
            rows.append((a, b) if a % 2 else (b, a))
    return rows, endpoint


def quotient(count, rows):
    parts = Components(2*count)
    for head, tail in rows:
        assert head % 2 == 1 and tail % 2 == 0
        parts.join(head, tail)
    return [(parts.root(2*i), parts.root(2*i+1)) for i in range(count)]


def neighbors(edges):
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    return adj


def colorable(edges):
    if any(u == v for u, v in edges):
        return False
    adj = neighbors(edges)
    paint = {}
    def extend():
        if len(paint) == len(adj):
            return True
        choices = [(set(range(3)) - {paint[x] for x in nb if x in paint}, v)
                   for v, nb in adj.items() if v not in paint]
        allowed, v = min(choices, key=lambda item: (len(item[0]), -len(adj[item[1]])))
        for c in allowed:
            paint[v] = c
            if extend():
                return True
            del paint[v]
        return False
    return extend()


def obstruction_time(count, weighted_rows):
    """Local merge times of final components with at most three ports."""
    parts = Components(2*count)
    for _, (h, t) in weighted_rows:
        parts.join(h, t)
    groups = {}
    for p in range(2*count):
        groups.setdefault(parts.root(p), []).append(p)
    assert all(len(ps) <= 3 for ps in groups.values())
    distance = {(p, p): 0 for ps in groups.values() for p in ps}
    for time, (p, q) in weighted_rows:
        distance[p, q] = distance[q, p] = min(time, distance.get((p, q), float('inf')))
    for ps in groups.values():
        for k, i, j in product(ps, repeat=3):
            distance[i, j] = min(distance.get((i, j), float('inf')),
                                 max(distance.get((i, k), float('inf')),
                                     distance.get((k, j), float('inf'))))
    events = []
    for i in range(count):
        if parts.root(2*i) == parts.root(2*i+1):
            events.append(distance[2*i, 2*i+1])
    adj = neighbors(quotient(count, [row for _, row in weighted_rows]))
    for v, nb in adj.items():
        comp = nb | {v}
        if len(comp) == 4 and all(adj[u] == comp - {u} for u in comp):
            events.append(max(distance[i, j] for u in comp
                              for i, j in product(groups[u], repeat=2)))
    return min(events, default=float('inf'))


def capped_diamonds(n):
    edges = []
    for i in range(n):
        a, b = n + 1 + 2*i, n + 2 + 2*i
        edges.extend([(a, b), (i, a), (i, b), (i+1, a), (i+1, b)])
    return 3*n+1, edges + [(0, n)]


EDGES = (
    (0, 1), (0, 4), (0, 6), (0, 9), (1, 2), (1, 5), (1, 7),
    (2, 6), (2, 8), (3, 4), (3, 7), (4, 5), (4, 8), (5, 10),
    (5, 11), (6, 10), (6, 11), (7, 8), (7, 11), (8, 10), (9, 11),
)
TERMINALS = (3, 9)


def triangle_free_block():
    degrees = Counter(v for edge in EDGES for v in edge)
    edge_set = set(EDGES)
    assert len(edge_set) == 21 and max(degrees.values()) == 4
    assert all(degrees[v] == 2 for v in TERMINALS)
    assert not any({(a, b), (a, c), (b, c)} <= edge_set for a, b, c in combinations(range(12), 3))
    counts = Counter()
    x, y = TERMINALS
    for colors in product(range(3), repeat=12):
        if all(colors[a] != colors[b] for a, b in EDGES):
            counts[colors[x], colors[y]] += 1
    assert counts == {(0, 0): 10, (1, 1): 10, (2, 2): 10}
    print(f"Audited {3**12} assignments. Proper colorings per terminal pair: {dict(sorted(counts.items()))}")


def clause_graph(variables, clauses):
    # Vertices 0,1,2 serve as false,true,base. Fresh pairs represent a variable
    # and its complement, in that order. Signed literal names start at one.
    order = 3
    edges = [(0, 1), (1, 2), (0, 2)]
    def pair():
        nonlocal order
        p = order
        order += 2
        edges.extend([(p, p+1), (p, 2), (p+1, 2)])
        return p
    def nae(literals):
        nonlocal order
        a = order
        order += 3
        edges.extend([(a, a+1), (a+1, a+2), (a, a+2)])
        edges.extend((a+i, x) for i, x in enumerate(literals))
    starts = [pair() for _ in range(variables)]
    for clause in clauses:
        a, b, c = [starts[abs(lit)-1] + int(lit < 0) for lit in clause]
        z = pair()
        nae((a, b, z))
        nae((z+1, c, 0))
    return order, edges


def split_high_degree(order, edges):
    ends = [list(edge) for edge in edges]
    incidence = [[] for _ in range(order)]
    for i, (a, b) in enumerate(edges):
        incidence[a].append((i, 0))
        incidence[b].append((i, 1))
    internal = []
    for positions in incidence:
        if len(positions) <= 4:
            continue
        shared = None
        leaves = []
        for j in range(len(positions)-2):
            anchors = [order, order+1]
            next_port = order+2
            ports = ([shared] if shared is not None else [])
            fresh = 3-len(ports)
            ports.extend(range(next_port, next_port+fresh))
            order = next_port+fresh
            internal.append(tuple(anchors))
            internal.extend((a, p) for a in anchors for p in ports)
            used = {shared}
            if j+1 < len(positions)-2:
                shared = ports[-1]
                used.add(shared)
            leaves.extend(p for p in ports if p not in used)
        assert len(leaves) == len(positions)
        for (i, side), new in zip(positions, leaves):
            ends[i][side] = new
    return order, [tuple(edge) for edge in ends]+internal


def color_with_common_neighbors(edges):
    # In any proper three-coloring, all common neighbors of the endpoints
    # of one edge have the third color. Contract them, then use exact search.
    while edges and all(u != v for u, v in edges):
        adj = neighbors(edges)
        parts = Components(1 + max(adj))
        changed = False
        for u, v in edges:
            common = adj[u] & adj[v]
            if len(common) > 1:
                first = next(iter(common))
                for other in common:
                    if parts.root(first) != parts.root(other):
                        parts.join(first, other)
                        changed = True
        if not changed:
            break
        edges = list({tuple(sorted((parts.root(u), parts.root(v)))) for u, v in edges})
    return colorable(edges)


def check_clause_reduction():
    instances = [
        (1, []), (1, [(1, 1, 1)]), (1, [(1, 1, 1), (-1, -1, -1)]),
        (2, [(1, 1, -2), (2, 2, -1), (-1, -2, -2)]),
        (3, [(1, 2, 3), (-1, -2, -3), (-1, 3, 3), (2, -3, 1)]),
    ]
    alphabet = [(1, 1, 1), (-1, -1, -1), (2, 2, 2), (-2, -2, -2)]
    instances.extend((2, sub) for r in range(5) for sub in combinations(alphabet, r))
    for variables, clauses in instances:
        expected = any(all(any(bool(values[abs(l)-1]) != (l < 0) for l in c)
                           for c in clauses) for values in product(range(2), repeat=variables))
        order, edges = split_high_degree(*clause_graph(variables, clauses))
        assert max(map(len, neighbors(edges).values()), default=0) <= 4
        rows, _ = make_paths(order, edges)
        assert color_with_common_neighbors(quotient(len(edges), rows)) == expected
    return len(instances)


def main():
    triangle_free_block()
    print(f"{check_clause_reduction()} end-to-end 3-CNF reductions passed")
    possible = list(combinations(range(5), 2))
    rng = Random(82761)
    graph_count = 0
    cases = 0
    for mask in range(1 << len(possible)):
        edges = [e for i, e in enumerate(possible) if mask >> i & 1]
        rows, origin = make_paths(5, edges)
        components = Components(2*len(edges))
        for h, t in rows:
            assert origin[h] == origin[t] and components.root(h) != components.root(t)
            components.join(h, t)
        assert len({components.root(i) for i in range(2*len(edges))}) == len(set(origin))
        assert colorable(edges) == colorable(quotient(len(edges), rows))
        graph_count += 1
        if max(map(len, neighbors(edges).values()), default=0) <= 3:
            weighted = [(rng.randrange(1, 5), row) for row in rows]
            birth = obstruction_time(len(edges), weighted)
            for t in range(5):
                active = [r for w, r in weighted if w <= t]
                assert (t < birth) == colorable(quotient(len(edges), active))
                cases += 1

    # Include final loops, parallel quotient edges, duplicate rows and tied weights.
    for _ in range(700):
        m = rng.randrange(1, 9)
        remaining = list(range(2*m))
        rng.shuffle(remaining)
        weighted = []
        while remaining:
            size = min(len(remaining), rng.randrange(1, 4))
            ps, remaining = remaining[:size], remaining[size:]
            for h in ps:
                for t in ps:
                    if h % 2 and not t % 2:
                        weighted.append((rng.randrange(1, 5), (h, t)))
                        weighted.append((rng.randrange(1, 5), (h, t)))
        birth = obstruction_time(m, weighted)
        for t in range(5):
            assert (t < birth) == colorable(quotient(m, [r for w, r in weighted if w <= t]))
            cases += 1

    deletions = 0
    for n in range(1, 8):
        order, edges = capped_diamonds(n)
        rows, _ = make_paths(order, edges)
        assert not colorable(quotient(len(edges), rows))
        assert len(rows) == 7*n+1
        for i in range(len(rows)):
            assert colorable(quotient(len(edges), rows[:i]+rows[i+1:]))
            deletions += 1
    print(f"{graph_count} orientations and quotients, {cases} threshold checks, "
          f"{deletions} single-row deletions passed")


if __name__ == "__main__":
    main()
