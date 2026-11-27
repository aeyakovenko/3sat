"""Finite checks for the candidate-model repair rule."""

from itertools import combinations, product


def subsets(vertices, capacity):
    for size in range(1, min(capacity, len(vertices)) + 1):
        yield from combinations(vertices, size)


def repair_runs(violations, capacity, retained=frozenset()):
    available = tuple(i for i, row in enumerate(violations) if row.isdisjoint(retained))
    if not available:
        yield ()
        return
    for batch in subsets(available, capacity):
        new_retained = retained.union(*(violations[i] for i in batch))
        for later in repair_runs(violations, capacity, new_retained):
            yield (batch,) + later


def graph_runs(neighborhoods, capacity, survivors):
    if not survivors:
        yield ()
        return
    for batch in subsets(sorted(survivors), capacity):
        deleted = set().union(*(neighborhoods[i] for i in batch))
        for later in graph_runs(neighborhoods, capacity, survivors - deleted):
            yield (batch,) + later


def audit_graphs(n):
    vertices = tuple(range(n))
    edges = tuple(combinations(vertices, 2))
    for indicators in product((False, True), repeat=len(edges)):
        # Private unit clause i is violated by model i alone.
        violations = [{i} for i in vertices]
        neighborhoods = [{i} for i in vertices]
        for clause, ((u, v), present) in enumerate(zip(edges, indicators), n):
            if present:
                violations[u].add(clause)
                violations[v].add(clause)
                neighborhoods[u].add(v)
                neighborhoods[v].add(u)

        for capacity in (1, 2):
            actual = set(repair_runs(violations, capacity))
            predicted = set(graph_runs(neighborhoods, capacity, set(vertices)))
            assert actual == predicted
            if capacity == 1:
                completed = {frozenset(batch[0] for batch in run) for run in actual}
                maximal_independent = set()
                for choice in subsets(vertices, n):
                    chosen = set(choice)
                    independent = all((neighborhoods[i] & chosen) == {i} for i in chosen)
                    dominates = set().union(*(neighborhoods[i] for i in chosen)) == set(vertices)
                    if independent and dominates:
                        maximal_independent.add(frozenset(chosen))
                assert completed == maximal_independent


def one_hot_models(r):
    for selectors in product((False, True), repeat=r):
        for flags in product((False, True), repeat=r + 1):
            if flags[0] or not flags[-1]:
                continue
            if all(flags[j + 1] == (flags[j] or bit) and not (flags[j] and bit)
                   for j, bit in enumerate(selectors)):
                yield selectors


def audit_blockers(r):
    models = list(one_hot_models(r))
    assert len(models) == len(set(models)) == r
    clauses = tuple(product(range(r), repeat=3))
    violations = []
    for x, y, z in product(models, repeat=3):
        violated = {index for index, (i, j, k) in enumerate(clauses) if x[i] and y[j] and z[k]}
        assert len(violated) == 1
        violations.append(violated)
    assert len(set.union(*violations)) == r**3
    if r == 2:
        total_missing = 0
        for mask in range(1 << len(clauses)):
            retained = {i for i in range(len(clauses)) if mask & (1 << i)}
            survivors = [row for row in violations if row.isdisjoint(retained)]
            assert len(survivors) == len(clauses) - len(retained)
            total_missing += len(survivors)
        assert 2 * total_missing == len(clauses) * (1 << len(clauses))


if __name__ == "__main__":
    for order in range(1, 6):
        audit_graphs(order)
    for group_size in range(1, 5):
        audit_blockers(group_size)
    print("All graphs on 1–5 vertices, capacities 1 and 2, and blocker groups of sizes 1–4 passed.")
