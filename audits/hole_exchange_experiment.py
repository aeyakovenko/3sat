"""Exhaust finite matching omissions and check signed-minor weights exactly."""

from fractions import Fraction
from itertools import permutations
from random import Random

from sympy import Matrix


def reachable(matching, allowed):
    free = next(z for z in range(len(matching) + 1) if z not in matching)
    seen = {free}
    todo = [free]
    while todo:
        label = todo.pop()
        for row, matched in enumerate(matching):
            if matched not in seen and allowed[row] & (1 << label):
                seen.add(matched)
                todo.append(matched)
    return seen


def check_graphs(rows):
    width = rows + 1
    assignments = list(permutations(range(width), rows))
    full_mask = (1 << width) - 1
    compatible = 0
    for bits in range(1 << (rows * width)):
        allowed = [(bits >> (row * width)) & full_mask for row in range(rows)]
        matchings = [
            f for f in assignments if all(mask & (1 << z) for mask, z in zip(allowed, f))
        ]
        holes = {next(z for z in range(width) if z not in f) for f in matchings}
        for f in matchings:
            assert reachable(f, allowed) == holes
        compatible += len(matchings)
    return 1 << (rows * width), compatible


def check_minors(rng):
    tested = 0
    for rows in range(1, 6):
        for _ in range(12):
            matrix = Matrix(rows, rows + 1, lambda *_: rng.randint(-3, 3))
            minors = []
            for col in range(rows + 1):
                submatrix = matrix.copy()
                submatrix.col_del(col)
                minors.append((-1) ** col * int(submatrix.det()))
            if not any(minors):
                assert matrix.rank() < rows
                continue
            assert all(value == 0 for value in matrix * Matrix(minors))
            total = sum(value**2 for value in minors)
            for col, signed_minor in enumerate(minors):
                if not signed_minor:
                    continue
                submatrix = matrix.copy()
                submatrix.col_del(col)
                solution = submatrix.inv() * matrix.col(col)
                assert Fraction(signed_minor**2, total) == 1 / (1 + solution.dot(solution))
            tested += 1
    return tested


if __name__ == "__main__":
    counts = [check_graphs(rows) for rows in range(1, 4)]
    print(sum(c[0] for c in counts), "graphs,", sum(c[1] for c in counts), "compatible matchings")
    print(check_minors(Random(82)), "full-rank integer matrices")
