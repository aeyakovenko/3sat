"""Find and exhaustively check one small projection game. Python standard library."""

from collections import deque
from itertools import combinations
from random import Random


def parity(bits):
    return bits.bit_count() % 2


def solve_instance():
    n, m = 8, 14
    triples = Random(29).sample(list(combinations(range(n), 3)), m)
    rows = [sum(1 << i for i in t) for t in triples]
    syndromes = {
        sum(parity(row & x) << j for j, row in enumerate(rows))
        for x in range(1 << n)
    }
    # Multi-source BFS gives the exact distance to the set of planted syndromes.
    distance = {w: 0 for w in syndromes}
    queue = deque(syndromes)
    while queue:
        w = queue.popleft()
        for j in range(m):
            v = w ^ (1 << j)
            if v not in distance:
                distance[v] = distance[w] + 1
                queue.append(v)
    gap = max(distance.values())
    rhs = min(w for w, d in distance.items() if d == gap)
    assert gap > 0

    dependencies = [0] * (1 << m)
    min_dependency = min_conflict = m + 1
    for mask in range(1, 1 << m):
        bit = mask & -mask
        total = dependencies[mask ^ bit] ^ rows[bit.bit_length() - 1]
        dependencies[mask] = total
        if total == 0:
            min_dependency = min(min_dependency, mask.bit_count())
            if parity(rhs & mask):
                min_conflict = min(min_conflict, mask.bit_count())
    assert min_dependency <= min_conflict <= m
    # Every reply sequence on any d-1 indices occurs on a planted instance.
    for positions in combinations(range(m), min_dependency - 1):
        mask = sum(1 << j for j in positions)
        assert len({w & mask for w in syndromes}) == 1 << len(positions)

    hub = n
    adj = [set() for _ in range(n + 1 + m + n)]
    def connect(v, u):
        adj[v].add(u)
        adj[u].add(v)
    for j, t in enumerate(triples):
        for v in t:
            connect(n + 1 + j, v)
    for i in range(n):
        connect(n + 1 + m + i, i)
        connect(n + 1 + m + i, hub)
    diameter = 0
    for source in range(len(adj)):
        dist = {source: 0}
        queue = deque([source])
        while queue:
            v = queue.popleft()
            for u in adj[v] - dist.keys():
                dist[u] = dist[v] + 1
                queue.append(u)
        assert len(dist) == len(adj)
        diameter = max(diameter, max(dist.values()))
    assert diameter <= 6

    # Score all bit labelings, locally optimizing the label at each projection node.
    best = 3 * m
    for x in range(1 << n):
        cost = 0
        for j, t in enumerate(triples):
            actual = sum(((x >> v) & 1) << k for k, v in enumerate(t))
            legal = [a for a in range(8) if parity(a) == ((rhs >> j) & 1)]
            assert len(legal) == 4
            assert all(sum((a >> k) & 1 for a in legal) == 2 for k in range(3))
            cost += min((a ^ actual).bit_count() for a in legal)
        # Auxiliary nodes can choose their two endpoints' values at zero cost.
        best = min(best, cost)
    assert best == gap
    edges = sum(map(len, adj)) // 2
    print(f"{n} bits, {m} primary equations, RHS {rhs:#x}, graph diameter {diameter}.")
    print(f"Minimum failed edges {best}/{edges}. Smallest row dependence "
          f"{min_dependency}, smallest inconsistent subsystem {min_conflict}.")
    print(f"All responses on any {min_dependency - 1} RHS indices extend to a planted YES.")

if __name__ == "__main__":
    solve_instance()
