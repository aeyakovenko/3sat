"""Exact cut-rank experiment on quadratic phases of the 3- and 4-cubes."""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb


def binary_rank(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def rational_rank(rows):
    matrix = [list(map(Fraction, row)) for row in rows]
    rank = 0
    for column in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        for row in range(rank + 1, len(matrix)):
            scale = matrix[row][column] / matrix[rank][column]
            if scale:
                matrix[row] = [x - scale*y for x, y in zip(matrix[row], matrix[rank])]
        rank += 1
    return rank


def embed(value, positions):
    return sum(((value >> i) & 1) << p for i, p in enumerate(positions))


def run(dimension):
    n = 1 << dimension
    neighbors = [sum(1 << (v ^ (1 << j)) for j in range(dimension)) for v in range(n)]
    hist = Counter()
    for left in combinations(range(n), n // 2):
        right = [v for v in range(n) if v not in left]
        right_mask = sum(1 << v for v in right)
        r = binary_rank(neighbors[v] & right_mask for v in left)
        hist[r] += 1
        if dimension == 3:
            def phase(assignment):
                edges = sum((assignment & neighbors[v]).bit_count() for v in range(n)
                            if (assignment >> v) & 1) // 2
                return (-1) ** (edges % 2)
            rows = [[phase(embed(a, left) | embed(b, right)) for b in range(1 << len(right))]
                    for a in range(1 << len(left))]
            assert rational_rank(rows) == 1 << r
    cut_load = 2 * comb(n - 2, n // 2 - 1)
    score = Fraction(sum(r * count for r, count in hist.items()), cut_load)
    assert sum(hist.values()) == comb(n, n // 2) and score <= n - 1
    print(f"Q{dimension}: k={n}, histogram={dict(sorted(hist.items()))}, "
          f"uniform balanced-cut score={score}, universal cap={n - 1}")


if __name__ == "__main__":
    run(3)
    run(4)
