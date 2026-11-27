"""Compile and solve the four 3-CNFs for every menu of three two-probe codes.

Each code is a four-bit truth table reading the two physical tag signs of its
input. This finite example exercises the list construction's self-reference.
The offering programs here only inspect those two signs.
"""

from itertools import combinations, product
from struct import Struct
from time import perf_counter

from first_missing_offer_audit import first_deficient_prefix


# The header gives variable and clause counts. Each literal occupies one byte:
# the high bit is its sign, and the other seven bits give its variable number.
HEADER = Struct('>BH')
SIGN = 128
FALSE_VAR = 3
CODE_COUNT = 3
LEVEL_COUNT = CODE_COUNT + 1


def prefix_clauses(level):
    pins = [-(i + 1) if level & (1 << i) else i + 1 for i in range(2)]
    return [(pin, FALSE_VAR, FALSE_VAR) for pin in pins] + [(-FALSE_VAR,) * 3]


def literal_bytes(clauses):
    return bytes(abs(lit) | (SIGN if lit < 0 else 0) for clause in clauses for lit in clause)


def offers(code, formula):
    # Only these two byte addresses may be inspected by the code.
    low = formula[HEADER.size] >> 7
    high = formula[HEADER.size + 3] >> 7
    return bool(code & (1 << (low + 2 * high)))


def selector(row, code):
    return 4 + CODE_COUNT * row + code


def compile_list(menu):
    # Each physical prefix is determined before the menu-dependent body is
    # emitted. The programs ignore the header, so its counts can be filled last.
    prefixes = [literal_bytes(prefix_clauses(h)) for h in range(LEVEL_COUNT)]
    provisional = [bytes(HEADER.size) + pins for pins in prefixes]
    clauses = []
    last_var = selector(LEVEL_COUNT - 1, CODE_COUNT - 1)

    def emit(literals):
        nonlocal last_var
        remaining = tuple(literals)
        while len(remaining) > 3:
            last_var += 1
            clauses.append((*remaining[:2], last_var))
            remaining = (-last_var, *remaining[2:])
        clauses.append(remaining + (remaining[-1],) * (3 - len(remaining)))

    # Pins 1 and 2 are false precisely when their raw sign bit is set. A
    # positive pin literal therefore disables an implication on a zero bit.
    # Level 0 enables row 0. Rows 1, 2 and 3 need lo OR hi, hi, and lo AND hi.
    guards = [[()], [(1,), (2,)], [(2,)], [(1, 2)]]
    for h in range(LEVEL_COUNT):
        choices = [selector(h, e) for e in range(CODE_COUNT)]
        for guard in guards[h]:
            emit((*guard, *choices))
        for a, b in combinations(choices, 2):
            emit((-a, -b))
        for e, code in enumerate(menu):
            # A tautology reserves the same record size as a forbidden entry.
            emit((FALSE_VAR, -FALSE_VAR) if offers(code, provisional[h]) else (-choices[e],))

    for e in range(CODE_COUNT):
        for a, b in combinations(range(LEVEL_COUNT), 2):
            emit((-selector(a, e), -selector(b, e)))

    assert last_var < SIGN
    header = HEADER.pack(last_var, 3 + len(clauses))
    body = literal_bytes(clauses)
    return [header + pins + body for pins in prefixes]


def decode(formula):
    var_count, clause_count = HEADER.unpack_from(formula)
    assert len(formula) == HEADER.size + 3 * clause_count
    clauses = []
    for offset in range(HEADER.size, len(formula), 3):
        clause = set()
        for byte in formula[offset:offset + 3]:
            variable = byte & (SIGN - 1)
            assert 1 <= variable <= var_count
            clause.add(-variable if byte & SIGN else variable)
        if not any(-lit in clause for lit in clause):
            clauses.append(tuple(clause))
    return clauses


def assign(clauses, literal):
    return [tuple(x for x in clause if x != -literal) if -literal in clause else clause
            for clause in clauses if literal not in clause]


def satisfiable(clauses):
    """DPLL on decoded clauses without information about rows or codes."""
    while clauses:
        shortest = min(clauses, key=len)
        if not shortest:
            return False
        lit = shortest[0]
        if len(shortest) > 1:
            return satisfiable(assign(clauses, lit)) or satisfiable(assign(clauses, -lit))
        clauses = assign(clauses, lit)
    return True


def check_all():
    start = perf_counter()
    boundaries = [0] * LEVEL_COUNT
    for menu in product(range(16), repeat=CODE_COUNT):
        formulas = compile_list(menu)
        for h, formula in enumerate(formulas):
            expected = bytearray(formulas[0])
            for bit in range(2):
                expected[HEADER.size + 3 * bit] ^= ((h >> bit) & 1) << 7
            assert formula == expected

        # This second execution reads the actual final serialized neighbors.
        rows = [sum(1 << e for e, code in enumerate(menu) if offers(code, formula))
                for formula in formulas]
        first = first_deficient_prefix(rows, CODE_COUNT)
        truth = [satisfiable(decode(formula)) for formula in formulas]
        assert truth == [h < first for h in range(LEVEL_COUNT)]
        for e in range(CODE_COUNT):
            if not any(truth[h] and rows[h] & (1 << e) for h in range(LEVEL_COUNT)):
                assert not rows[first] & (1 << e)
        boundaries[first] += 1
    total = sum(boundaries)
    print(f'{total} menus, {LEVEL_COUNT * total} serialized 3-CNFs, first missing counts {boundaries}')
    print(f'{len(formulas[0])} bytes per formula, {perf_counter() - start:.2f} seconds')


if __name__ == '__main__':
    check_all()
