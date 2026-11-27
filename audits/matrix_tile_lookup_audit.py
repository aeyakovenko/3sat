"""Finite checks for simultaneous Ferrers trimming and the matrix-tile SAT encoding."""

from itertools import combinations_with_replacement, product
from math import isqrt
from random import Random

from packed_sat_forest_audit import pin, satisfiable, xor_gate


def admissible_starts(shape, width):
    """(row start, column start) for all contained squares of the given width."""
    side = len(shape)
    return {(i, j) for i, j in product(range(side - width + 1), repeat=2)
            if j >= side - shape[i + width - 1]}


def audit_trimming(side):
    shapes = [values[::-1] for values in combinations_with_replacement(range(side + 1), side)]
    placements = {(shape, width): admissible_starts(shape, width)
                  for shape in shapes for width in range(1, side + 1)}
    for a, b, z in product(shapes, repeat=3):
        holes = 3 * side**2 - sum(a) - sum(b) - sum(z)
        width = side - isqrt(4 * holes // 3)
        if width > 0:
            assert any((j, k) in placements[b, width] and (k, i) in placements[z, width]
                       for i, j in placements[a, width] for k in range(side - width + 1))
    return len(shapes)**3


def bit(matrix, i, j, d):
    return matrix >> (i * d + j) & 1


def product_table(d):
    h = d * d
    table = []
    for a, b in product(range(1 << h), repeat=2):
        entries = [(sum(bit(a, i, k, d) * bit(b, k, j, d) for k in range(d)) & 1)
                   for i, j in product(range(d), repeat=2)]
        table.append(sum(value << index for index, value in enumerate(entries)))
    return table


def direct_trace(row, d):
    a, b, z = row
    return sum(bit(a, i, j, d) * bit(b, j, k, d) * bit(z, k, i, d)
               for i, j, k in product(range(d), repeat=3)) & 1


def audit_matrix_layout():
    d = 2
    h = d * d
    alphabet = 1 << h
    products = product_table(d)
    table = {}
    for row in product(range(alphabet), repeat=3):
        a, b, z = row
        ab = products[(a << h) | b]
        by_product = sum(bit(ab, i, j, d) * bit(z, j, i, d)
                         for i, j in product(range(d), repeat=2)) & 1
        assert by_product == direct_trace(row, d)
        table[row] = by_product

    rng = Random(1117)
    trials = 0
    for steps in range(1, 6):
        for _ in range(35):
            rows = [tuple(rng.randrange(alphabet) for _ in range(3)) for _ in range(steps)]
            if rng.randrange(2) and len(rows) > 1:
                rows[-1] = rows[0]
            parity = alphabet**3 + 1
            dummies = (parity + steps + 1, parity + steps + 2)
            position = {(a, b, z): 1 + (a << (2 * h)) + (b << h) + z for a, b, z in rows}
            # Removing unused pinned variables preserves satisfiability for all dummy bits.
            clauses = [clause for row, slot in position.items() for clause in pin(slot, table[row], *dummies)]
            clauses += pin(parity, 0, *dummies) + pin(parity + steps, 1, *dummies)
            for i, row in enumerate(rows):
                clauses.extend(xor_gate(parity + i, position[row], parity + i + 1))
            assert satisfiable(clauses) == bool(sum(direct_trace(row, d) for row in rows) % 2)
            trials += 1
    return len(table), trials


if __name__ == "__main__":
    shapes = sum(audit_trimming(d) for d in range(1, 4))
    entries, formulas = audit_matrix_layout()
    print(f"{shapes} triangle masks, {entries} trace-table positions, {formulas} tiled CNFs passed")
