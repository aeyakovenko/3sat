"""Exhaust small affine subspaces, parity dictionaries, and value-aware accesses."""

from functools import cache
from itertools import product


@cache
def subspaces(n):
    """Each new pivot is the leading bit of e_n + one coset of the old space."""
    if n == 0:
        return ((0,),)
    pivot = 1 << (n - 1)
    spaces = []
    for space in subspaces(n - 1):
        spaces.append(space)
        remaining = set(range(pivot))
        while remaining:
            shift = min(remaining)
            coset = {v ^ shift for v in space}
            remaining -= coset
            spaces.append(space + tuple(sorted(pivot | v for v in coset)))
    return tuple(spaces)


def ip(v, half):
    return ((v >> half) & v & ((1 << half) - 1)).bit_count() % 2


def affine_on(table, space):
    basis = []
    span = {0}
    for v in space:
        if v not in span:
            basis.append(v)
            span.update({s ^ v for s in span})
    return all(table[a ^ u] ^ table[a] == table[u] ^ table[0]
               for a in space for u in basis)


def check_witt():
    cases = 0
    for half in (1, 2, 3):
        n = 2 * half
        valid = [space for space in subspaces(n)
                 if affine_on([ip(v, half) for v in range(1 << n)], space)]
        assert max(len(space) for space in valid) == 1 << half
        for x in range(1 << n):
            max_const = max(len(space) for space in valid
                            if all(ip(x ^ v, half) == ip(x, half) for v in space))
            assert max_const == 1 << (half - ip(x, half))
            cases += 1
    return cases


def check_scanner():
    cases = 0
    # Two independent dictionary occurrences, evaluated by two genuine lookups.
    for count, half in ((2, 1), (3, 1), (1, 2)):
        b = 2 * half
        n = count * b
        mask = (1 << b) - 1
        rows = [[ip((x >> (j*b)) & mask, half) for x in range(1 << n)] for j in range(count)]
        # Affineness is translation-independent for these quadratic rows.
        valid = [space for space in subspaces(n) if all(affine_on(row, space) for row in rows)]
        answers = [sum(row[x] for row in rows) % 2 for x in range(1 << n)]
        for x in range(1 << n):
            best = max(len(space) for space in valid
                       if all(answers[x ^ v] == answers[x] for v in space))
            any_one = any(row[x] for row in rows)
            assert best == 1 << (n // 2 - any_one)
            cases += 1
    return cases


def check_clauses():
    def unit(lit):
        return (lit, lit, lit)

    cases = 0
    p = 4
    for names in product(range(p), repeat=p):
        clauses = [unit(p + v if ip(v, 1) else -(p + v)) for v in range(p)]
        a = p + names[0]
        for j, name in enumerate(names[1:], 1):
            b = p + name
            c = 2 * p + j
            clauses.extend(((a, b, -c), (a, -b, c), (-a, b, c), (-a, -b, -c)))
            a = c
        clauses.append(unit(a))
        variables = sorted({abs(lit) for clause in clauses for lit in clause})
        satisfying = 0
        for assignment in product((False, True), repeat=len(variables)):
            values = dict(zip(variables, assignment))
            satisfying += all(any(values[abs(lit)] == (lit > 0) for lit in clause)
                              for clause in clauses)
        assert satisfying == sum(ip(v, 1) for v in names) % 2
        cases += 1
    return cases


def check_changing_addresses():
    # Each x selects a different address. Reading the register from an affine
    # table, or writing its old value back through x, preserves all affine cells.
    n = 4
    points = tuple(range(1 << n))
    table = [v ^ 9 for v in points]
    assert affine_on(table, points)
    for address in points:
        cell_after_store = [table[x] if x == address else table[address] for x in points]
        assert affine_on(cell_after_store, points)


if __name__ == '__main__':
    print('Basepoints with sharp translated Witt dimensions:', check_witt())
    print('Basepoints with sharp per-lookup and terminal restrictions:', check_scanner())
    print('Ordinary dictionary 3-CNFs checked on every assignment:', check_clauses())
    check_changing_addresses()
    print('No rank cost for an affine moving load and moving no-op store.')
