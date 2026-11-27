"""Exhaustive model checks for sampled weighted formulas and small summary families."""

from itertools import product
from random import Random


def satisfies(clause, assignment):
    return any(bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0) for lit in clause)


def horn_parts(clause):
    positive = [lit for lit in clause if lit > 0]
    assert len(positive) <= 1
    return (positive[0] if positive else 0), {-lit for lit in clause if lit < 0}


def first_firings(rules):
    # A rule carries its originating row ID, or None for an auxiliary branch rule.
    marked, retained = set(), set()
    for threshold in sorted({weight for weight, _, _, _ in rules}):
        while True:
            before = len(marked)
            for weight, head, body, row_id in rules:
                if weight <= threshold and head not in marked and body <= marked:
                    marked.add(head)
                    if row_id is not None:
                        retained.add(row_id)
            if len(marked) == before:
                break
    return retained


def certificate(formula, n, guarded):
    exceptional, orig_horn = [], []
    for pos, (weight, clause) in enumerate(formula):
        if sum(lit > 0 for lit in clause) > 1:
            exceptional.append(pos)
        else:
            head, body = horn_parts(clause)
            orig_horn.append((weight, head, body, pos))
    retained = set(exceptional)
    branch_count = 0
    options = []
    for pos in exceptional:
        clause = formula[pos][1]
        if guarded:
            options.append([lit for lit in clause if lit > 0])
        else:
            options.append(clause)
    for choice in product(*options):
        aux = []
        for pos, lit in zip(exceptional, choice):
            if guarded:
                head = lit
                body = {-v for v in formula[pos][1] if v < 0}
            else:
                head, body = horn_parts((lit,))
            aux.append((formula[pos][0], head, body, None))
        retained.update(first_firings(orig_horn + aux))
        branch_count += 1
    assert len(retained) <= len(exceptional) + (n + 1) * branch_count
    return [formula[pos] for pos in sorted(retained)]


def models_at(formula, threshold, n):
    active = [clause for weight, clause in formula if weight <= threshold]
    return [m for m in range(1 << n) if all(satisfies(clause, m) for clause in active)]


def minimal(models):
    return {m for m in models if all(q == m or q & m != q for q in models)}


def all_negative_answers(models, n):
    # A query is any subset of all 2^n negative clauses, including the empty clause.
    bodies = range(1 << n)
    violated_sets = [sum(1 << body for body in bodies if m & body == body) for m in models]
    return [any(q & violated == 0 for violated in violated_sets) for q in range(1 << (1 << n))]


def audit_thresholds():
    rng = Random(20261125)
    threshold_cases = negative_cases = 0
    for trial in range(200):
        n = 3 + trial % 4
        rows = []
        for j in range(12):
            width = rng.choice((1, 2, 2, 3, 3))
            vars_ = rng.sample(range(1, n + 1), width)
            if j < (trial // 4) % 4:
                width = rng.choice((2, 3))
                vars_ = rng.sample(range(1, n + 1), width)
                positive_count = rng.randint(2, width)
            else:
                positive_count = rng.randint(0, 1)
            clause = tuple(v if i < positive_count else -v for i, v in enumerate(vars_))
            if j == 11 and trial % 9 == 0:
                clause = ()
            rows.append((rng.randrange(4), clause))
        certificates = [certificate(rows, n, guarded) for guarded in (False, True)]
        for t in range(-1, 4):
            full = models_at(rows, t, n)
            candidates = [models_at(retained, t, n) for retained in certificates]
            assert all(minimal(full) == minimal(small) for small in candidates)
            threshold_cases += 1
            if n == 3:
                full_answers = all_negative_answers(full, n)
                assert all(full_answers == all_negative_answers(small, n) for small in candidates)
                negative_cases += len(full_answers)
    return threshold_cases, negative_cases


def selector_bank(start, depth):
    """Depth zero or one. Return leaf IDs, background rows, and negative query pins."""
    if depth == 0:
        return start + 1, [start], [(start,)], [()]
    assert depth == 1
    digits = tuple(range(start, start + 3))
    root = start + 3
    leaves = list(range(root + 1, root + 4))
    background = [digits, (root,)] + [(-root, -d, leaf) for d, leaf in zip(digits, leaves)]
    pins = [tuple(-d for d in digits if d != selected) for selected in digits]
    return root + 4, leaves, background, pins


def free_bank(start):
    leaves = [start, start + 1]
    return start + 2, leaves, [], [(leaf,) for leaf in leaves]


def audit_summary(positive_budget):
    fresh = 1
    background = []
    leaf_ids, pins = [], []
    for bank_id in range(2):
        if bank_id < positive_budget:
            fresh, leaves, rows, queries = free_bank(fresh)
        else:
            depth = int(positive_budget == 1 or bank_id == 0)
            fresh, leaves, rows, queries = selector_bank(fresh, depth)
        background.extend(rows)
        leaf_ids.append(leaves)
        pins.append(queries)
    outputs = [fresh, fresh + 1]
    n = outputs[-1]
    triples = list(product(range(len(leaf_ids[0])), range(len(leaf_ids[1])), range(2)))
    implications, unit_queries = [], []
    for i, j, k in triples:
        implications.append((-leaf_ids[0][i], -leaf_ids[1][j], outputs[k]))
        query = pins[0][i] + pins[1][j] + (-outputs[k],)
        assert sum(lit > 0 for lit in query) == positive_budget
        unit_queries.append(query)

    # Enumerate unrestricted assignments to all variables, including optional leaves.
    # Each surviving mask is the set of candidate implications falsified by that model.
    masks = [set() for _ in triples]
    for m in range(1 << n):
        if not all(satisfies(clause, m) for clause in background):
            continue
        violated = sum(1 << i for i, clause in enumerate(implications) if not satisfies(clause, m))
        for i, query in enumerate(unit_queries):
            if all(satisfies((lit,), m) for lit in query):
                masks[i].add(violated)
    relation_count = 1 << len(triples)
    for relation in range(relation_count):
        decoded = 0
        for i, possible_violations in enumerate(masks):
            satisfiable = any(relation & violations == 0 for violations in possible_violations)
            if not satisfiable:
                decoded |= 1 << i
        assert decoded == relation
    return relation_count, relation_count * len(triples)


if __name__ == "__main__":
    thresholds, negative_queries = audit_thresholds()
    print(f"{thresholds} minimal-model comparisons and {negative_queries} negative-query checks passed.")
    total = 0
    for p in (0, 1, 2):
        relations, answers = audit_summary(p)
        total += answers
        print(f"p={p}: {relations} relations and {answers} query answers passed.")
    print(f"{total} single-position query answers passed.")
