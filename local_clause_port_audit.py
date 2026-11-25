"""Finite checks for ternary-clause replacements on a fixed boundary."""
from collections import Counter
from itertools import combinations, product


def all_rows(variables):
    return [tuple(v * s for v, s in zip(scope, signs))
            for scope in combinations(range(1, variables + 1), 3)
            for signs in product((1, -1), repeat=3)]


def satisfying_mask(row, variables):
    result = 0
    for assignment in range(1 << variables):
        if any(bool(assignment & (1 << (abs(lit) - 1))) == (lit > 0)
               for lit in row):
            result |= 1 << assignment
    return result


def two_row_exhaustion():
    variables = 6
    rows = all_rows(variables)
    full = (1 << (1 << variables)) - 1
    masks = {row: satisfying_mask(row, variables) for row in rows}

    def project(mask):
        projected = 0
        for offset in range(0, 1 << variables, 8):
            projected |= (mask >> offset) & 255
        return projected

    target = 254
    found = set()
    for left, right in combinations(rows, 2):
        if project(masks[left] & masks[right]) != target:
            continue
        if any(project(mask) == target for mask in (masks[left], masks[right])):
            continue
        found.add(frozenset((frozenset(left), frozenset(right))))
    predicted = set()
    for pivot, shared in product(range(4, 7), range(1, 4)):
        a, c = sorted({1, 2, 3} - {shared})
        for sign in (1, -1):
            predicted.add(frozenset((frozenset((shared, a, sign * pivot)),
                                     frozenset((shared, c, -sign * pivot)))))
    assert found == predicted
    assert project(full) == 255
    return len(rows) * (len(rows) - 1) // 2, len(found)


def forbidden_patterns(rows, variables, ports):
    masks = [satisfying_mask(row, variables) for row in rows]
    counts = []
    for boundary in range(1 << ports):
        assignments = range(boundary, 1 << variables, 1 << ports)
        counts.append(sum(all(mask >> z & 1 for mask in masks) for z in assignments))
    deletions = []
    for i in range(len(rows)):
        deletions.append(sum(all(j == i or mask >> z & 1 for j, mask in enumerate(masks))
                             for z in range(0, 1 << variables, 1 << ports)))
    return counts, deletions


def nonsingular_successors():
    # Port indices 1, 2, 3; the auxiliary cube coordinates are 4, 5, 6.
    rows = [(1, 5, 6), (2, 4, -6), (3, -4, -5),
            (4, -5, 6), (-4, 5, -6)]
    counts, deletions = forbidden_patterns(rows, 6, 3)
    assert counts == [2 * i.bit_count() for i in range(8)]
    assert deletions == [2, 2, 2, 1, 1]
    assert Counter(abs(x) for row in rows for x in row) == {1: 1, 2: 1, 3: 1, 4: 4, 5: 4, 6: 4}

    # Lift two rows with common p,q, while keeping a new pair with two common literals.
    pair = [(1, 2, 3), (1, 2, 4)]
    image = [(1, 2, 5), (-5, 1, 3), (-5, 1, 4)]
    old, _ = forbidden_patterns(pair, 4, 4)
    new, _ = forbidden_patterns(image, 5, 4)
    assert [n > 0 for n in new] == [n > 0 for n in old]

    # Start from all eight clauses on three variables. Each row-deletion has a private model.
    rest = [r for r in all_rows(3) if r not in ((1, 2, 3), (1, 2, -3))]
    shared, second = 1, 2
    for z in range(4, 13):
        rest.append((shared, second, z))
        shared, second = -z, shared
        family = rest + [(shared, second, 3), (shared, second, -3)]
        private = [False] * len(family)
        for assignment in range(1 << z):
            failed = [index for index, row in enumerate(family)
                      if all(bool(assignment & (1 << (abs(lit) - 1))) != (lit > 0)
                             for lit in row)]
            assert failed
            if len(failed) == 1:
                private[failed[0]] = True
        assert all(private)
        assert min(Counter(abs(lit) for row in family for lit in row).values()) >= 3
    return counts, deletions, len(family)


if __name__ == "__main__":
    pairs, exact = two_row_exhaustion()
    counts, deletions, final_size = nonsingular_successors()
    print(f"Checked {pairs} two-row formulas, with precisely {exact} essential replacements.")
    print(f"Five-row extension counts {counts}; one-row deletions at zero {deletions}.")
    print(f"Two-parent lift preserved all private rows through {final_size} clauses.")
