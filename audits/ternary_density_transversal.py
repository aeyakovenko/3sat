"""Check the density bound and the small-transversal algorithm on finite families."""
from itertools import combinations, product


def mask_of(vertices):
    return sum(1 << v for v in vertices)


def cover_number(edges, n):
    for size in range(n + 1):
        for members in combinations(range(n), size):
            candidate = mask_of(members)
            if all(e & candidate for e in edges):
                return size
    raise AssertionError("an empty hyperedge has no transversal")


def assignment_columns(n, edges):
    full = (1 << (1 << n)) - 1
    return [[full ^ sum(1 << x for x in range(1 << n) if (x & e) == key)
             for key in range(1 << n) if (key & e) == key] for e in edges]


def check_signed(n):
    edges = [mask_of(v) for v in combinations(range(n), 3)]
    columns = assignment_columns(n, edges)
    full = (1 << (1 << n)) - 1
    checked = 0
    for selected in range(1 << len(edges)):
        indices = [i for i in range(len(edges)) if (selected >> i) & 1]
        tau = cover_number([edges[i] for i in indices], n)
        max_models = 0
        for signs in product(range(8), repeat=len(indices)):
            models = full
            for i, sign in zip(indices, signs):
                models &= columns[i][sign]
            max_models = max(max_models, models.bit_count())
            assert models.bit_count() * (8 ** tau) <= (1 << n) * (7 ** tau)
            checked += 1
        monotone = full
        for i in indices:
            monotone &= columns[i][-1]
        assert monotone.bit_count() == max_models
    return checked


def submasks(s):
    t = s
    while t:
        yield t
        t = (t - 1) & s
    yield 0


def kernel(edges, k):
    kept = []
    counts = {}
    caps = [(k + 1) ** (3 - i) for i in range(4)]
    for e in edges:
        ss = list(submasks(e))
        if any(counts.get(s, 0) >= caps[s.bit_count()] for s in ss):
            continue
        kept.append(e)
        for s in ss:
            counts[s] = counts.get(s, 0) + 1
    return kept


def feasible(edges, budget):
    if budget < 0:
        return False
    if not edges:
        return True
    e = edges[0]
    pair = next((other for other in edges[1:] if e & other), None)

    def take(points):
        return feasible([s for s in edges if not s & points], budget - points.bit_count())

    if pair is None:
        return feasible(edges[1:], budget - 1)
    common = e & pair
    if any(take(1 << i) for i in range(common.bit_length()) if (common >> i) & 1):
        return True
    return any(take((1 << i) | (1 << j))
               for i in range(e.bit_length()) if ((e ^ common) >> i) & 1
               for j in range(pair.bit_length()) if ((pair ^ common) >> j) & 1)


def check_uniform(n):
    edges = [mask_of(v) for v in combinations(range(n), 3)]
    # Each independent-set bit is one complete assignment on n variables.
    full = (1 << (1 << n)) - 1
    monotone = [row[-1] for row in assignment_columns(n, edges)]
    layers = [sum(1 << x for x in range(1 << n) if x.bit_count() == s)
              for s in range(n + 1)]
    checked = 0

    def visit(i, used, models):
        nonlocal checked
        if i < len(edges):
            visit(i + 1, used, models)
            used.append(edges[i])
            visit(i + 1, used, models & monotone[i])
            used.pop()
            return
        alpha = next(s for s in range(n, -1, -1) if layers[s] & models)
        tau = n - alpha
        assert models.bit_count() * (8 ** tau) <= (1 << n) * (7 ** tau)
        if n <= 5:
            assert cover_number(used, n) == tau
            for k in range(4):
                kept = kernel(used, k)
                assert len(kept) <= (k + 1) ** 3
                assert feasible(kept, k) == (tau <= k)
                for points in range(1 << n):
                    if points.bit_count() <= k:
                        assert all(e & points for e in used) == all(e & points for e in kept)
        checked += 1

    visit(0, [], full)
    return checked


if __name__ == '__main__':
    print("Signed catalogs with at most one clause per support:", check_signed(4))
    for size in (5, 6):
        print(f"All monotone ternary hypergraphs on {size} vertices:", check_uniform(size))
