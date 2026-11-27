"""Finite checks for narrow DAG proofs and small tree proofs of pinned closed circuits."""

from functools import cache
from itertools import product
from math import comb


def rail(gate, value):
    return 2 * gate + int(value) + 1


def forward_clauses(gates):
    """Return all local implications, the actual values, and one honest row per gate."""
    values = []
    rows = set()
    honest = []
    for index, gate in enumerate(gates):
        if isinstance(gate, int):
            value = gate
            actual = frozenset({rail(index, value)})
            rows.add(actual)
        else:
            left, right, table = gate
            for a, b in product(range(2), repeat=2):
                output = table >> (2*a + b) & 1
                clause = frozenset({-rail(left, a), -rail(right, b), rail(index, output)})
                rows.add(clause)
            x, y = values[left], values[right]
            value = table >> (2*x + y) & 1
            actual = frozenset({-rail(left, x), -rail(right, y), rail(index, value)})
        values.append(value)
        honest.append(actual)
    return rows, values, honest


def resolve(positive, negative, pivot):
    assert pivot in positive and -pivot in negative
    return (positive - {pivot}) | (negative - {-pivot})


def check_proofs(gates):
    rows, values, honest = forward_clauses(gates)
    goal = rail(len(gates)-1, values[-1])
    wrong_pin = frozenset({-goal})
    units = set()
    for index, row in enumerate(honest):
        assert row in rows and len(row) <= 3
        derived = row
        for minus_literal in sorted(row):
            if minus_literal > 0:
                continue
            pivot = -minus_literal
            assert pivot in units
            derived = resolve(frozenset({pivot}), derived, pivot)
            assert len(derived) <= 3
        target = rail(index, values[index])
        assert derived == {target}
        units.add(target)
    assert not resolve(frozenset({goal}), wrong_pin, goal)

    # Work up the continuing branch of the comb, independently checking the
    # prefix invariant and every used inference against its two parents.
    continuing = wrong_pin
    nodes = 1
    for index in reversed(range(len(gates))):
        pivot = rail(index, values[index])
        zero_child = honest[index]
        assert pivot in zero_child
        if -pivot in continuing:
            continuing = resolve(zero_child, continuing, pivot)
            nodes += 2
        prefix = {rail(i, val) for i, val in enumerate(values[:index])}
        assert all(-literal in prefix for literal in continuing)
    assert not continuing and nodes <= 2*len(gates) + 1

    # The least model satisfies every clause and the correct pin.
    assert all(any((abs(lit) in units) == (lit > 0) for lit in clause) for clause in rows)
    assert rail(len(gates)-1, 1-values[-1]) not in units


def audit_closed_circuits():
    count = 0
    # Two gates after the input, allowing repeated parents, constants as truth
    # tables, nonmonotone tables, and reuse of an earlier value.
    for value, first in product(range(2), range(16)):
        for left, right, last in product(range(2), range(2), range(16)):
            check_proofs([value, (0, 0, first), (left, right, last)])
            count += 1
    for x, y, first, last in product(range(2), range(2), range(16), range(16)):
        check_proofs([x, y, (0, 1, first), (2, 0, last)])
        count += 1
    print(f'{count} closed circuits checked for both pins, DAG width and comb inferences')


@cache
def shape_counts(leaves):
    """Distribution of pending-sibling depths, with counts of ordered trees."""
    if leaves == 1:
        return {0: 1}
    result = {}
    for a in range(1, leaves):
        b = leaves-a
        for l, left_count in shape_counts(a).items():
            for r, right_count in shape_counts(b).items():
                depth = max(1+l, r) if a <= b else max(1+r, l)
                result[depth] = result.get(depth, 0) + left_count * right_count
    return result


def audit_pending():
    total = 0
    for leaves in range(1, 33):
        histogram = shape_counts(leaves)
        number = sum(histogram.values())
        assert number == comb(2*leaves-2, leaves-1) // leaves
        assert all(2**p <= leaves for p in histogram)
        assert max(histogram) == leaves.bit_length()-1
        total += number
    print(f'{total} ordered tree shapes through 32 leaves counted by pending-stack depth')


if __name__ == '__main__':
    audit_closed_circuits()
    audit_pending()
