"""Exhaust the five-clause forced-bit catalog and check the two sharp pin gadgets."""

from collections import Counter
from itertools import combinations, permutations, product
from math import comb


FIVE = ((1, 2, 4), (1, -3, -4), (1, -2, 3), (2, 3, -4), (-2, -3, 4))
SIX = ((1, -2, -3), (1, 2, 4), (1, 2, -4),
       (-2, 3, 5), (3, -5, 6), (3, -5, -6))


def truth_table(clauses, variable_count):
    return sum(1 << bits for bits in range(1 << variable_count)
               if all(any(bool(bits & (1 << (abs(lit) - 1))) == (lit > 0) for lit in row)
                      for row in clauses))


def normalize(clauses):
    return tuple(sorted(tuple(sorted(row, key=abs)) for row in clauses))


def check_gadgets():
    for rows, n, expected_excess in ((FIVE, 4, 3), (SIX, 6, 2)):
        models = truth_table(rows, n)
        assert models and all(bits & 1 for bits in range(1 << n) if models & (1 << bits))
        assert models & (1 << ((1 << n) - 1))
        assert sum(all(lit > 0 for lit in row) for row in rows) == 1
        assert all(any(lit > 0 for lit in row) for row in rows)
        degree = Counter(abs(lit) for row in rows for lit in row)
        assert degree[1] == 3 and max(degree.values()) == 4
        assert sum(max(0, count - 3) for count in degree.values()) == expected_excess


def orbit_of_five():
    orbit = set()
    for permutation in permutations((2, 3, 4)):
        for signs in product((1, -1), repeat=3):
            rename = {1: 1} | {i: j * s for i, j, s in zip((2, 3, 4), permutation, signs)}
            orbit.add(normalize(tuple(rename[abs(z)] if z > 0 else -rename[abs(z)]
                                      for z in row) for row in FIVE))
    return orbit


def exhaust():
    clauses = [tuple(i * sign for i, sign in zip(names, signs))
               for names in combinations(range(1, 5), 3)
               for signs in product((1, -1), repeat=3)]
    tables = [truth_table([row], 4) for row in clauses]
    masks = [sum(1 << (abs(lit) - 1) for lit in row) for row in clauses]
    even_assignments = sum(1 << bits for bits in range(0, 16, 2))
    full = (1 << 16) - 1
    pins = set()
    checked = 0
    for size in range(6):
        for candidate in combinations(range(len(clauses)), size):
            checked += 1
            models = full
            for row_id in candidate:
                models &= tables[row_id]
            if not models or models & even_assignments:
                continue
            degrees = [sum(bool(masks[row_id] & (1 << bit)) for row_id in candidate)
                       for bit in range(4)]
            if degrees[0] <= 3 and max(degrees) <= 4:
                assert size == 5
                pins.add(normalize([clauses[row_id] for row_id in candidate]))
    assert checked == sum(comb(32, i) for i in range(6))
    assert pins == orbit_of_five() and len(pins) == 8
    print(f'{checked:,} clause subsets through five rows; {len(pins)} pins form one signed orbit')


if __name__ == '__main__':
    check_gadgets()
    exhaust()
