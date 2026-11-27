"""Check the finite permanent-grid specializations used in pr249-bit-probes.md."""

from functools import lru_cache
from itertools import combinations, permutations, product
from math import factorial
from random import Random

import sympy as sp


def permanent(matrix):
    return sum(
        sp.prod(matrix[i][j] for i, j in enumerate(sigma))
        for sigma in permutations(range(len(matrix)))
    )


def check_level(m, pivot, pattern, alphabet):
    entries = iter(pattern)
    matrix = []
    pivot_symbol = sp.Symbol("pivot")
    for i in range(m):
        row = []
        for j in range(m):
            if (i, j) == pivot:
                row.append(pivot_symbol)
            else:
                value = next(entries)
                row.append(value or sp.Symbol(f"x{i}{j}"))
        matrix.append(row)
    f = permanent(matrix)
    a = f.diff(pivot_symbol)
    b = f.subs(pivot_symbol, 0)
    candidate = factorial(m) * alphabet**m + 1
    assert not sp.gcd(a, b - candidate).free_symbols
    assert sp.cancel(f.subs(pivot_symbol, (candidate - b) / a) - candidate) == 0


def check_minor(m, free_rows, free_cols):
    scale = sp.Symbol("scale")
    matrix = [
        [sp.Integer(1 + (i + 2*j) % 3) for j in range(m)] for i in range(m)
    ]
    block = [[sp.Symbol(f"z{i}{j}") for j in free_cols] for i in free_rows]
    for r, i in enumerate(free_rows):
        for c, j in enumerate(free_cols):
            matrix[i][j] = scale * block[r][c]
    complement = [
        [matrix[i][j] for j in range(m) if j not in free_cols]
        for i in range(m) if i not in free_rows
    ]
    leading = sp.expand(permanent(matrix)).coeff(scale, len(free_rows))
    assert sp.expand(leading - permanent(block) * permanent(complement)) == 0


def enlarged_permanent(m, u, v):
    size = m * m + m
    rows = [[] for _ in range(size)]
    for edge, (i, j) in enumerate(product(range(m), repeat=2)):
        private = m + edge
        rows[i].append((private, u[edge]))
        rows[private].extend([(j, 1), (private, v[edge])])

    @lru_cache(maxsize=None)
    def complete(used):
        if used.bit_count() == size:
            return 1
        return sum(
            value * complete(used | (1 << column))
            for column, value in rows[used.bit_count()]
            if not (used >> column) & 1
        )

    return complete(0)


def check_integer_pivot(m, rng):
    size = m * m
    u = [rng.randint(1, 7) for _ in range(size)]
    v = [rng.randint(1, 7) for _ in range(size)]
    pivot = rng.randrange(size)
    a = b = 0
    for matching in permutations(range(m)):
        chosen = {row * m + column for row, column in enumerate(matching)}
        term = 1
        for edge in range(size):
            if edge != pivot:
                term *= u[edge] if edge in chosen else v[edge]
        if pivot in chosen:
            a += term
        else:
            b += term
    assert enlarged_permanent(m, u, v) == a * u[pivot] + b * v[pivot] > 0
    scale = rng.randint(1, 7)
    u[pivot], v[pivot] = -scale * b, scale * a
    assert enlarged_permanent(m, u, v) == 0


if __name__ == "__main__":
    level_checks = 0
    for pivot in product(range(2), repeat=2):
        for pattern in product(range(3), repeat=3):
            check_level(2, pivot, pattern, 2)
            level_checks += 1
    rng = Random(249)
    for _ in range(108):
        pivot = (rng.randrange(3), rng.randrange(3))
        pattern = [rng.randrange(3) for _ in range(8)]
        check_level(3, pivot, pattern, 2)
        level_checks += 1

    minor_checks = 0
    for m in (2, 3, 4):
        for k in range(1, m + 1):
            for rows in combinations(range(m), k):
                for cols in combinations(range(m), k):
                    check_minor(m, rows, cols)
                    minor_checks += 1
    for m in (2, 3, 4):
        for _ in range(20):
            check_integer_pivot(m, rng)
    print(f"{level_checks} level specializations; {minor_checks} minor coefficients; 60 integer pivots")
