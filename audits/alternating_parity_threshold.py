"""Enumerate parity certificates with one probe and at most k challenges."""

from functools import reduce
from itertools import combinations, product
from operator import and_


def clause_tables(k):
    """Truth tables of nonempty, non-tautological clauses, with duplicates removed."""
    result = []
    for signs in product((-1, 0, 1), repeat=k):
        if not any(signs):
            continue
        table = 0
        for x in range(1 << k):
            if any(sign and ((x >> i) & 1) == (sign == 1) for i, sign in enumerate(signs)):
                table |= 1 << x
        result.append(table)
    return result


def has_cycle_structure(table, k):
    vertices = [x for x in range(1 << k) if table & (1 << x)]
    differences = {x ^ vertices[0] for x in vertices}
    nonempty = differences - {0}
    blocks = [x for x in nonempty if not any(y != x and (y & x) == y for y in nonempty)]
    if any(x.bit_count() % 2 for x in blocks) or any(x & y for x, y in combinations(blocks, 2)):
        return False
    unions = {0}
    for x in blocks:
        unions |= {y | x for y in unions}
    return unions == differences


def check(k):
    clauses = clause_tables(k)
    full = (1 << (1 << k)) - 1
    even = sum(1 << x for x in range(1 << k) if x.bit_count() % 2 == 0)
    odd = full ^ even
    passing = set()
    inspected = 0
    for m in range(k + 1):
        for choice in combinations(clauses, m):
            inspected += 1
            table = reduce(and_, choice, full)
            if table and (table & even == 0 or table & odd == 0):
                passing.add(table)
    assert all(has_cycle_structure(table, k) for table in passing)
    maximum = max(table.bit_count() for table in passing)
    assert maximum == 1 << (k // 2)
    print(f'k={k}: {inspected} CNFs, {len(passing)} nonempty one-sign tables, maximum {maximum} vertices')


if __name__ == '__main__':
    for dimension in range(1, 5):
        check(dimension)
