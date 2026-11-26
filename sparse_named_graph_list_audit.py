"""Check named-edge graph encodings independently of their width bounds."""

from collections import Counter, defaultdict, deque
from itertools import combinations, permutations, product


def graph_from_records(records):
    graph = defaultdict(set)
    for left, right in records:
        assert left != right and right not in graph[left]
        graph[left].add(right)
        graph[right].add(left)
    return graph


def distances(graph, source):
    queue = deque([source])
    distance = {source: 0}
    while queue:
        left = queue.popleft()
        for right in graph[left]:
            if right not in distance:
                distance[right] = distance[left] + 1
                queue.append(right)
    return distance


def build(left, right):
    m = len(left)
    assert m == len(right) and m > 0 and not (m & (m - 1))
    size = 2 * m
    edges = []
    endpoints = []
    for side, labels in enumerate((left, right)):
        # Heap indices 1..size-1 are internal; size+i denotes leaf i.
        nodes = {j: ('node', side, j) for j in range(1, 2 * size)}
        nodes.update({size+i: ('key', value) for i, value in enumerate(labels)})
        for j in range(2, 2 * size):
            edges.append((nodes[j//2], nodes[j]))
        endpoints.append((nodes[1], nodes[size+m]))
    source, ground = ('root',), ('ground',)
    edges.extend([(endpoints[0][1], endpoints[1][1]),
                  (source, endpoints[0][0]), (ground, endpoints[1][0])])
    return edges, source, ground


def check_pair(left, right):
    m = len(left)
    common = len(set(left) & set(right))
    edges, source, ground = build(left, right)
    graph = graph_from_records(edges)
    dist = distances(graph, source)
    assert len(dist) == len(graph)
    assert len(edges) + 1 - len(graph) == common
    assert max(map(len, graph.values())) <= 3
    assert (all((dist[x]-dist[y]) % 2 for x, y in edges)) == (common == 0)
    expected = 2 * m.bit_length() + 3 - bool(common)
    assert dist[ground] == expected

    incidence = [(('edge', i), v) for i, pair in enumerate(edges) for v in pair if v != ground]
    expanded = graph_from_records(incidence)
    assert len(distances(expanded, source)) == len(expanded)
    assert len(expanded[source]) == 1 and max(map(len, expanded.values())) <= 3
    # The selected column vertices of a shortest path give precisely the
    # required open-neighborhood syndrome; the longer private path does too.
    def switches(along):
        selected = {frozenset(pair) for pair in zip(along, along[1:])}
        flips = {('edge', i) for i, e in enumerate(edges) if frozenset(e) in selected}
        lit = {u for u, neighbors in expanded.items() if len(neighbors & flips) % 2}
        assert lit == {source}
        return len(flips)

    path = [ground]
    while path[-1] != source:
        v = path[-1]
        path.append(next(u for u in graph[v] if dist[u] + 1 == dist[v]))
    assert switches(path) == expected
    # Ignore all shared keys to recover the supplied path without their aid.
    private_graph = graph_from_records([(u, v) for u, v in edges
                                        if u[0] != 'key' and v[0] != 'key'])
    private = distances(private_graph, source)
    path = [ground]
    while path[-1] != source:
        v = path[-1]
        path.append(next(u for u in private_graph[v] if private[u] + 1 == private[v]))
    assert switches(path) == 2 * m.bit_length() + 3

    ports = graph_from_records([(('private', j), ('key', val))
                                for j, val in enumerate((*left, *right))])
    assert sum(len(neighbors) == 2 for neighbors in ports.values()) == common
    assert (max(map(len, ports.values())) == 1) == (common == 0)
    return expected == len(path)-1


def check_signed():
    count = 0
    for raw in product(range(4), repeat=2):
        left = tuple((0, i, val) for i, val in enumerate(raw))
        parity = 0
        for target in combinations(range(4), 2):
            for tags in product(range(2), repeat=2):
                inner = 0
                for active in product(range(2), repeat=2):
                    right = tuple((0, tags[j], target[j]) if use else (1, j, 0)
                                  for j, use in enumerate(active))
                    assert len(set(left)) == len(set(right)) == 2
                    inner ^= check_pair(left, right)
                    count += 1
                assert inner == all(raw[tags[j]] == target[j] for j in range(2))
                parity ^= inner
        assert parity == (raw[0] != raw[1])
    return count


if __name__ == '__main__':
    totals = Counter()
    for m in (1, 2, 4):
        left = tuple(range(m))
        for right in permutations(range(2*m), m):
            assert check_pair(left, right) == set(left).isdisjoint(right)
            totals[len(set(left) & set(right))] += 1
    print(f'{sum(totals.values())} distinct test pairs grouped by intersection size: {dict(totals)}')
    print(f'{check_signed()} valid signed graph terms on 16 unrestricted raw lists')
