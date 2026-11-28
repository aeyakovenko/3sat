"""Independently test the model-density loss for disjoint intersecting pairs."""
from functools import lru_cache
from itertools import combinations, product


def mask(vertices):
    return sum(1 << v for v in vertices)


class Rows:
    def __init__(self, n):
        self.n = n
        self.count = 1 << n
        self.full = (1 << self.count) - 1
        self.columns = []
        for i in range(n):
            run = 1 << i
            # Periodic bit positions with the ith variable set.
            block = ((1 << run) - 1) << run
            self.columns.append(block * (self.full // ((1 << (2 * run)) - 1)))
        self.layers = [0] * (n + 1)
        # A bitset by cardinality, without repeated shifts into a large integer.
        bytes_in_layer = [bytearray((self.count + 7) // 8) for _ in range(n + 1)]
        for x in range(self.count):
            bytes_in_layer[x.bit_count()][x >> 3] |= 1 << (x & 7)
        self.layers = [int.from_bytes(p, 'little') for p in bytes_in_layer]

    def models_of_clause(self, edge, falsifying_pattern):
        bad = self.full
        for v, column in enumerate(self.columns):
            if (edge >> v) & 1:
                bad &= column if (falsifying_pattern >> v) & 1 else self.full ^ column
        return self.full ^ bad

    def transversal(self, independent_rows):
        # Complements of independent sets are exactly the transversals.
        alpha = next(j for j in range(self.n, -1, -1)
                     if independent_rows & self.layers[j])
        return self.n - alpha

    def check(self, models, tau, packing):
        left = models.bit_count() * 8 ** tau * 49 ** packing
        right = self.count * 7 ** tau * 46 ** packing
        assert left <= right, (self.n, models.bit_count(), tau, packing)
        return left == right


def pair_packing(edges):
    unions = sorted({a | b for a, b in combinations(set(edges), 2) if a & b})

    @lru_cache(None)
    def optimum(i, used):
        if i == len(unions):
            return 0
        best = optimum(i + 1, used)
        if not (unions[i] & used):
            best = max(best, 1 + optimum(i + 1, unions[i] | used))
        return best

    return optimum(0, 0)


def uniform_order_six():
    rows = Rows(6)
    edges = [mask(t) for t in combinations(range(6), 3)]
    good = [rows.models_of_clause(e, e) for e in edges]
    checked = 0

    def visit(i, covered, paired, models):
        nonlocal checked
        if i == len(edges):
            # Each pair union has at least four vertices, and two cannot fit.
            rows.check(models, rows.transversal(models), int(paired))
            checked += 1
            return
        visit(i + 1, covered, paired, models)
        e = edges[i]
        visit(i + 1, covered | e, paired or bool(e & covered), models & good[i])

    visit(0, 0, False, rows.full)
    return checked


def signed_order_four():
    rows = Rows(4)
    edges = [mask(t) for t in combinations(range(4), 3)]
    checked = 0
    for enabled in range(1 << len(edges)):
        active = [e for j, e in enumerate(edges) if (enabled >> j) & 1]
        independent = rows.full
        for e in active:
            independent &= rows.models_of_clause(e, e)
        tau, paired = rows.transversal(independent), pair_packing(active)
        choices = [[rows.models_of_clause(e, x) for x in range(16) if (x & e) == x]
                   for e in active]
        for signed in product(*choices):
            models = rows.full
            for good in signed:
                models &= good
            rows.check(models, tau, paired)
            checked += 1
    return checked


def planted(copies):
    n = 5 * copies
    rows = Rows(n)
    base = [mask(x) for x in ((0, 1, 2), (0, 1, 3), (2, 3, 4))]
    edges = [e << (5 * j) for j in range(copies) for e in base]
    good = [rows.models_of_clause(e, e) for e in edges]
    # A planted signed version uses one fixed sign flip at each of these vertices.
    switched = mask(range(0, n, 3))
    signed = [rows.models_of_clause(e, e ^ (e & switched)) for e in edges]
    exact = 0
    for selected in range(1 << len(edges)):
        indices = [i for i in range(len(edges)) if (selected >> i) & 1]
        independent = rows.full
        models = rows.full
        for i in indices:
            independent &= good[i]
            models &= signed[i]
        assert independent.bit_count() == models.bit_count()
        tau = rows.transversal(independent)
        paired = pair_packing([edges[i] for i in indices])
        tight = rows.check(models, tau, paired)
        exact += int(tight)
        if len(indices) == len(edges):
            assert (tau, paired, models.bit_count()) == (2 * copies, copies, 23 ** copies)
            assert tight
    return 1 << len(edges), exact


if __name__ == '__main__':
    print('Four-variable signed catalogs:', signed_order_four())
    print('Six-vertex uniform hypergraphs:', uniform_order_six())
    for copies in (1, 2, 3):
        count, exact = planted(copies)
        print(f'{copies} planted copies: {count} support subsets checked, {exact} equality cases')
