"""Check the product decoder, a one-row repair, and a small minimax barrier."""
from collections import Counter
from heapq import heappop, heappush
from itertools import combinations, product

from threshold_port_coloring_audit import color_with_common_neighbors, make_paths, quotient


def kind(triple):
    return triple if len(set(triple)) == 3 else None


def conflicts(first, second):
    return sum(first[i] == second[j] for i in range(3) for j in range(3) if i != j)


def tensor_edges(edges):
    return [(3*x+i, 3*y+j) for x, y in edges
            for i in range(3) for j in range(3) if i != j]


def check_decoder():
    rows = list(product(range(3), repeat=3))
    bad = {(a, b): conflicts(a, b) for a, b in product(rows, repeat=2)}
    for a, b in product(rows, repeat=2):
        if bad[a, b] == 0:
            assert kind(a) == kind(b)
            if kind(a) is None:
                assert Counter(a).most_common(1)[0][0] != Counter(b).most_common(1)[0][0]
    for a, mid, b in product(rows, repeat=3):
        assert int(kind(a) != kind(b)) <= bad[a, mid] + bad[mid, b]


def split_and_paint(edges, planted):
    """Split high-degree vertices using chains of three-terminal equality gadgets."""
    colors = list(planted)
    ends = [list(e) for e in edges]
    incidence = [[] for _ in colors]
    for i, (a, b) in enumerate(edges):
        incidence[a].append((i, 0))
        incidence[b].append((i, 1))
    internal = []
    def fresh(color):
        colors.append(color)
        return len(colors)-1
    for v, slots in enumerate(incidence):
        if len(slots) <= 4:
            continue
        labels = [fresh(planted[v]) for _ in slots]
        pool = iter(labels)
        joints = [fresh(planted[v]) for _ in range(len(slots)-3)]
        for j in range(len(slots)-2):
            ports = (joints[j-1:j] if j else []) + joints[j:j+1]
            ports.extend(next(pool) for _ in range(3-len(ports)))
            a, b = [fresh(c) for c in range(3) if c != planted[v]]
            internal.append((a,b))
            internal.extend((x,p) for x in (a,b) for p in ports)
        for (i, side), label in zip(slots, labels):
            ends[i][side] = label
    return [tuple(e) for e in ends] + internal, colors


def check_physical_pin(order, graph, expected):
    edges = tensor_edges(graph)
    marked = len(edges)
    a, b = graph[0]
    edges.append((3*a, 3*b))
    split, colors = split_and_paint(edges, list(range(3))*order)
    assert [i for i, (x,y) in enumerate(split) if colors[x] == colors[y]] == [marked]
    target = split[marked][0]
    degree = sum(target in e for e in split)
    if degree == 3:
        split.append((target, len(colors)))
        colors.append((colors[target]+1) % 3)
    assert sum(target in e for e in split) == 4
    rows, owners = make_paths(len(colors), split)
    p = next(p for p in (2*marked, 2*marked+1) if owners[p] == target)
    same = [q for q, owner in enumerate(owners) if owner == target and q%2 == p%2 and q!=p]
    other = [q for q, owner in enumerate(owners) if owner == target and q%2 != p%2]
    assert len(same) == 1 and len(other) == 2
    target_path = [p, other[0], same[0], other[1]]
    rows = [r for r in rows if owners[r[0]] != target]
    replacement = [(u,v) if u%2 else (v,u) for u,v in zip(target_path, target_path[1:])]
    rows.extend(replacement[1:])
    seed = [colors[v] for v in owners]
    seed[p] = (seed[p]+1) % 3
    assert all(seed[i] != seed[i+1] for i in range(0, len(seed), 2))
    assert all(seed[u] == seed[v] for u, v in rows)
    h, t = replacement[0]
    assert seed[h] != seed[t]
    assert color_with_common_neighbors(quotient(len(split), rows+[replacement[0]])) == expected


def minimax_triangle():
    base = [(0,1), (1,2), (2,0)]
    edges = tensor_edges(base) + [(0,3)]
    states = list(product(range(3), repeat=9))
    costs = {s: sum(s[u] == s[v] for u,v in edges) for s in states}
    seed = (0,1,2)*3
    assert costs[seed] == 1
    # Weight of a path is the largest number of conflicts at any of its states.
    explored = {seed: 1}
    queue = [(1,seed)]
    while queue:
        worst, state = heappop(queue)
        if explored[state] != worst:
            continue
        if costs[state] == 0:
            return worst
        for i in range(9):
            for c in range(3):
                if c == state[i]:
                    continue
                nxt = state[:i]+(c,)+state[i+1:]
                value = max(worst,costs[nxt])
                if value < explored.get(nxt, len(edges)+1):
                    explored[nxt] = value
                    heappush(queue,(value,nxt))
    raise AssertionError("there is a row-constant solution")


def main():
    check_decoder()
    triangle = list(combinations(range(3), 2))
    check_physical_pin(3, triangle, True)
    check_physical_pin(4, list(combinations(range(4), 2)), False)
    check_physical_pin(5, [(0,1), (1,2), (2,3), (3,4), (4,0)], True)
    peak = minimax_triangle()
    assert peak == 2
    print(f"729 adjacent and 19683 midpoint configurations, 3 physical pin instances, "
          f"triangle minimum peak {peak} violated edges")


if __name__ == '__main__':
    main()
