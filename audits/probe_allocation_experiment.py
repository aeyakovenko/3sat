"""Exact checks for the distance formula in probe-allocation.md."""

from collections import deque
from fractions import Fraction as F
from itertools import combinations, product
from random import Random


def path_sampler(size, budget):
    if 2 * budget >= size:
        return [(tuple(range(parity, size, 2)), F(1, 2)) for parity in (0, 1)]
    return [
        (tuple((offset + 2 * j) % size for j in range(budget)), F(1, size))
        for offset in range(size)
    ]


def check_attainment(size, budget):
    samples = path_sampler(size, budget)
    gain = min(F(budget, size), F(1, 2))
    assert sum(weight for _, weight in samples) == 1
    assert max(len(bag) for bag, _ in samples) <= budget
    for v in range(size):
        assert sum(p for bag, p in samples if v in bag) == gain
    total = F(0)
    for bag, prob in samples:
        row_means = set()
        for answer in product((0, 1), repeat=len(bag)):
            bits = dict(zip(bag, answer))
            outside = 1 / (2 * (1 - gain))
            payoffs = [bits.get(0, outside)]
            for v in range(1, size):
                assert v not in bits or v - 1 not in bits
                if v in bits:
                    payoff = bits[v]
                elif v - 1 in bits:
                    payoff = 1 - bits[v - 1]
                else:
                    payoff = F(1, 2)
                payoffs.append(payoff)
            payoffs.append(1 - bits[size - 1] if size - 1 in bits else outside)
            assert all(0 <= val <= 1 for val in payoffs)
            row_means.add(sum(payoffs) / F(size + 1))
        assert len(row_means) == 1
        total += prob * row_means.pop()
    assert total == F(1, 2) + gain / (size + 1)


def check_layers(size, edges, sources, targets, bags):
    distance = {v: 0 for v in sources}
    todo = deque(sources)
    while todo:
        u = todo.popleft()
        for a, v in edges:
            if a == u and v not in distance:
                distance[v] = distance[u] + 1
                todo.append(v)
    if not any(v in distance for v in targets):
        return False
    depth = min(distance[v] for v in targets if v in distance)
    layers = [min(depth, distance.get(v, depth)) for v in range(size)]
    count = depth + 1
    marg = [sum(F(1, len(bags)) for bag in bags if v in bag) for v in range(size)]
    mass = [sum(marg[v] for v in range(size) if layers[v] == i) for i in range(count)]
    half = F(1, 2)
    caps = [min(half, mass[0])]
    caps.extend(min(half, u, v) for u, v in zip(mass, mass[1:]))
    caps.append(min(half, mass[-1]))
    if 0 in caps:
        cut = [F(int(i == caps.index(0))) for i in range(count + 1)]
    else:
        total = sum(1 / c for c in caps)
        cut = [1 / (c * total) for c in caps]
    budget = max(map(len, bags))
    bound = min(half, F(budget, count)) / (count + 1)
    for v in sources:
        assert sum(w for t, w in enumerate(cut) if layers[v] >= t) * min(half, marg[v]) <= bound
    for v in targets:
        assert sum(w for t, w in enumerate(cut) if layers[v] < t) * min(half, marg[v]) <= bound
    for u, v in edges:
        bad = sum(w for t, w in enumerate(cut) if layers[u] < t <= layers[v])
        assert bad * min(half, marg[u], marg[v]) <= bound
    return True


def run():
    for size in range(1, 13):
        for budget in range(1, size + 1):
            check_attainment(size, budget)
    tested = 0
    rng = Random(249)
    arcs = [(i, j) for i in range(3) for j in range(3) if i != j]
    for flags in product((False, True), repeat=len(arcs)):
        edges = [arc for arc, take in zip(arcs, flags) if take]
        for sources, targets in [({0}, {2}), ({0, 1}, {1, 2})]:
            for k in (1, 2, 3):
                bags = list(combinations(range(3), k))
                tested += check_layers(3, edges, sources, targets, bags)
    for _ in range(1500):
        size = rng.randrange(3, 10)
        edges = [(i, j) for i in range(size) for j in range(size) if rng.random() < 0.23]
        bags = [rng.sample(range(size), rng.randrange(1, size)) for _ in range(7)]
        tested += check_layers(size, edges, {0}, {size - 1}, bags)
    print(f"78 path sampler/budget checks and {tested} inconsistent graph/sampler checks passed")


if __name__ == "__main__":
    run()
