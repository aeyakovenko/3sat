"""Check the five-variable core, the optimizing transition, and constructed files."""
from itertools import combinations, product
from math import comb, prod


def optimizer(m):
    v0 = 3
    while comb(v0, 3) + v0 < m:
        v0 += 1
    deficit = m - (comb(v0 - 1, 3) + v0 - 1)
    if deficit <= 2:
        return v0 - 1, deficit
    return v0, 0


def construction(m):
    v, twos = optimizer(m)
    # Indices 1..5 form the directed cyclic core.
    pins = [(i + 1, -((i + 1) % 5 + 1), -((i + 2) % 5 + 1)) for i in range(5)]
    pins.extend((i, -1, -2) for i in range(6, v + 1))
    anchors = list(combinations(range(1, 6), 3))
    extra = [row for row in combinations(range(1, v + 1), 3) if row not in anchors]
    positive_count = m - v - twos
    clauses = pins + anchors + extra[:positive_count - len(anchors)]
    clauses.extend([(1, 2, -3), (1, -2, 3)][:twos])
    return v, clauses


def check_formula(m):
    v, clauses = construction(m)
    assert len(clauses) == m
    assert all(len({abs(x) for x in row}) == 3 for row in clauses)
    assert len({tuple(sorted(row)) for row in clauses}) == m
    solutions = []
    for x in product((False, True), repeat=v):
        if all(any(x[abs(lit) - 1] != (lit < 0) for lit in row) for row in clauses):
            solutions.append(x)
    assert solutions == [(True,) * v]
    true_counts = [sum(lit > 0 for lit in row) for row in clauses]
    expected_v, expected_twos = optimizer(m)
    assert true_counts.count(1) == expected_v
    assert true_counts.count(2) == expected_twos
    assert prod(true_counts) == 3 ** (m - v - expected_twos) * 2 ** expected_twos
    assert prod(2 ** t - 1 for t in true_counts) == 7 ** (m - v - expected_twos) * 3 ** expected_twos


def abstract_maximum(m, base, two):
    best = 0
    for v in range(3, m + 1):
        triples = min(comb(v, 3), m - v)
        best = max(best, base ** triples * two ** (m - v - triples))
    return best


def signed_optimum(twos, threes, budget):
    if budget <= twos:
        return 2 ** (twos - budget) * 3 ** threes
    remaining = budget - twos
    if remaining >= 2 * threes:
        return 1
    pairs, single = divmod(remaining, 2)
    return 2 ** single * 3 ** (threes - pairs - single)


def check_signed_envelope(m):
    v, twos = optimizer(m)
    for h in range(2 * m + 1):
        predicted = signed_optimum(twos, m - v - twos, h)
        candidates = []
        for num_vars in range(3, m + 1):
            triples = min(comb(num_vars, 3), m - num_vars)
            candidates.append(signed_optimum(m - num_vars - triples, triples, h))
        assert predicted == max(candidates)


if __name__ == "__main__":
    # The five anchor pins and all ten positive triples also give the m=15 core.
    for m in range(15, 101):
        check_formula(m)
    for m in range(16, 101):
        check_signed_envelope(m)
    for m in range(16, 501):
        v, twos = optimizer(m)
        for base, two in ((3, 2), (7, 3)):
            assert abstract_maximum(m, base, two) == base ** (m - v - twos) * two ** twos
    print("Unique assignments and clause patterns checked for m=15..100.")
    print("All signed-position budgets checked for m=16..100.")
    print("Both upper envelopes checked against all variable counts for m=16..500.")
