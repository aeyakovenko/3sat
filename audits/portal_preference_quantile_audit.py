"""Test threshold support using genuine off-tree spokes and repeated portal bottlenecks."""

from bisect import bisect_right
from itertools import combinations
from random import Random


def path_maxima(adjacency, start):
    maxima = {start: 0}
    stack = [start]
    while stack:
        here = stack.pop()
        for neighbor, weight in adjacency[here]:
            if neighbor not in maxima:
                maxima[neighbor] = max(maxima[here], weight)
                stack.append(neighbor)
    return maxima


def check_round(rng, size):
    adjacency = [[] for _ in range(size)]
    for i in range(1, size):
        parent = rng.randrange(i)
        weight = rng.randrange(1, 50)
        adjacency[i].append((parent, weight))
        adjacency[parent].append((i, weight))
    bottlenecks = [path_maxima(adjacency, i) for i in range(size)]
    portals = rng.sample(range(size), rng.randint(2, size))
    portal = [rng.choice(portals) for _ in range(size)]
    # A missing tree edge with this weight can be added as a supported spoke.
    weights = [bottlenecks[i][portal[i]] + rng.randrange(15) for i in range(size)]
    active = [(i, j) for i, j in combinations(range(size), 2)
              if portal[i] != portal[j] and rng.randrange(5)]
    by_endpoint = [[] for _ in range(size)]
    true = []
    for number, (i, j) in enumerate(active):
        key = bottlenecks[portal[i]][portal[j]]
        by_endpoint[i].append((key, number))
        by_endpoint[j].append((key, number))
        connected = bottlenecks[i][j] <= max(weights[i], weights[j])
        assert connected == (key <= weights[i] or key <= weights[j])
        true.append(connected)
    for t in (1, 2, 3, 5, 11):
        answer = [False] * len(active)
        for vertex, items in enumerate(by_endpoint):
            items.sort()
            stride = len(items) // (2 * t) + 1
            marks = [key for key, _ in items[stride - 1::stride]]
            rank = stride * bisect_right(marks, weights[vertex])
            for _, number in items[:rank]:
                answer[number] = True
        assert sum(x != y for x, y in zip(answer, true)) * t <= len(active)
    return len(active)


if __name__ == "__main__":
    rng = Random(312)
    count = sum(check_round(rng, size) for size in range(4, 30) for _ in range(10))
    print(f"{count} supported-spoke queries passed at five tolerances")
