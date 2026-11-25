"""Exhaustive binary checks of the cyclic centralizers and cubic polar forms."""

from fractions import Fraction
from itertools import product
from math import prod


def binary_rank(columns):
    pivots = {}
    for column in columns:
        while column:
            index = column.bit_length() - 1
            if index not in pivots:
                pivots[index] = column
                break
            column ^= pivots[index]
    return len(pivots)


def matrix_units(vertices, grade):
    return [(row, col)
            for i in range(3)
            for col in vertices[i]
            for row in vertices[(i + grade) % 3]]


def rank_count(rows, cols, rank):
    inject_left = prod((1 << rows) - (1 << i) for i in range(rank))
    inject_right = prod((1 << cols) - (1 << i) for i in range(rank))
    bases = prod((1 << rank) - (1 << i) for i in range(rank))
    return inject_left * inject_right // bases


def audit(shape):
    a, b, c = shape
    dim = a + b + c
    vertices = [range(a), range(a, a + b), range(a + b, dim)]
    spaces = [matrix_units(vertices, j) for j in range(3)]
    arrows = spaces[1]
    labels = {unit: i for i, unit in enumerate(arrows)}
    cycles = [(1 << labels[j, i]) | (1 << labels[k, j]) | (1 << labels[i, k])
              for i, j, k in product(*vertices)]
    size = 1 << len(arrows)
    truth = [sum((x & cycle) == cycle for cycle in cycles) % 2 for x in range(size)]
    actual = Fraction(size - 2 * sum(truth), size)
    predicted = sum(Fraction(rank_count(a, b, r), 1 << (a*b + c*r))
                    for r in range(min(a, b) + 1))
    assert actual == predicted
    if size == 8:
        terms = [0, 1, 2, 4, 3, 5, 6]
        best = 0
        for coefficients in range(1 << len(terms)):
            selected = [m for i, m in enumerate(terms) if coefficients >> i & 1]
            signed_sum = sum((-1) ** (truth[x] + sum((x & m) == m for m in selected))
                             for x in range(size))
            best = max(best, abs(signed_sum))
        assert Fraction(best, size) == actual

    moment_units = 0
    for u in range(size):
        rows = [0] * dim
        cols = [0] * dim
        for j, (r, s) in enumerate(arrows):
            if u >> j & 1:
                rows[r] |= 1 << s
                cols[s] |= 1 << (dim * r)
        # For the unit e_rs, u e_rs has column s from u and e_rs u has row r from u.
        def commutator(r, s):
            return (cols[r] << s) ^ (rows[s] << (dim * r))

        central = [len(units) - binary_rank(commutator(r, s) for r, s in units)
                   for units in spaces]
        c0, c1, c2 = central
        assert c2 - c0 == len(spaces[2]) - len(spaces[0])
        assert c1 <= c0 + c2

        derivative = lambda x: truth[x] ^ truth[x ^ u]
        polar = []
        for j in range(len(arrows)):
            column = 0
            e = 1 << j
            for k in range(len(arrows)):
                f = 1 << k
                if derivative(0) ^ derivative(e) ^ derivative(f) ^ derivative(e ^ f):
                    column |= f
            polar.append(column)
        polar_rank = binary_rank(polar)
        assert polar_rank == len(arrows) - c1
        assert polar_rank % 2 == 0
        moment_units += size >> (polar_rank // 2)
    rank_bound_squared = Fraction(moment_units, size * size)
    assert actual * actual <= rank_bound_squared
    return f"{shape}: {size} shifts, constant bias {actual}, polar second-moment bound {rank_bound_squared}"


if __name__ == "__main__":
    for dimensions in [(1, 1, 1), (1, 1, 3), (1, 2, 2), (1, 2, 3), (2, 2, 2)]:
        print(audit(dimensions))
