"""Test the line recovery in coded-hard-tables.md over GF(16)."""

from itertools import product
from functools import reduce
from operator import xor

Q = 16
MODULUS = 0b10011  # X^4 + X + 1


def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & Q:
            a ^= MODULUS
    return result


MUL = [[multiply(a, b) for b in range(Q)] for a in range(Q)]
INV = [0] + [MUL[a].index(1) for a in range(1, Q)]


def evaluate(coefficients, x):
    result = 0
    for coefficient in reversed(coefficients):
        result = MUL[result][x] ^ coefficient
    return result


def solve(rows, unknowns):
    """Return one solution of a consistent rectangular augmented system."""
    pivots = []
    for col in range(unknowns):
        rank = len(pivots)
        i = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if i is None:
            continue
        rows[rank], rows[i] = rows[i], rows[rank]
        inverse = INV[rows[rank][col]]
        rows[rank] = [MUL[inverse][v] for v in rows[rank]]
        for i, row in enumerate(rows):
            if i != rank and row[col]:
                scale = row[col]
                rows[i] = [v ^ MUL[scale][p] for v, p in zip(row, rows[rank])]
        pivots.append(col)
    assert all(any(row[:-1]) or not row[-1] for row in rows)
    coeff = [0] * unknowns
    for row, col in zip(rows, pivots):
        coeff[col] = row[-1]
    return coeff


def line_value(received, degree=2, errors=4):
    numerator_terms = degree + errors + 1
    system = []
    for t, y in enumerate(received):
        powers = [1]
        for _ in range(degree + errors):
            powers.append(MUL[powers[-1]][t])
        system.append(powers + [MUL[y][v] for v in powers[:errors + 1]])
    coeff = solve(system, numerator_terms + errors)
    remainder = coeff[:numerator_terms]
    denominator = coeff[numerator_terms:] + [1]
    quotient = [0] * (degree + 1)
    for shift in reversed(range(degree + 1)):
        factor = remainder[errors + shift]
        quotient[shift] = factor
        for j, v in enumerate(denominator):
            remainder[j + shift] ^= MUL[factor][v]
    assert not any(remainder)
    return quotient[0]


def binary_inner(a, z):
    return (a & z).bit_count() % 2


def main():
    for symbol in range(Q):
        word = [binary_inner(symbol, z) for z in range(Q)]
        for z in (0, 3, 11):
            word[z] ^= 1
        distances = [sum(binary_inner(a, z) != v for z, v in enumerate(word))
                     for a in range(Q)]
        assert distances.index(min(distances)) == symbol

    checks = 0
    # A bivariate multilinear polynomial with binary coefficients ranges
    # over all binary messages on {0,1}^2.
    for coeff in product(range(2), repeat=4):
        for x0, x1 in product(range(2), repeat=2):
            def poly(u, v):
                return reduce(xor, (MUL[a][b] for a, b in zip(coeff, [1, u, v, MUL[u][v]])))
            for slope in (0, 1, 3, 7):
                values = [poly(x0 ^ t, x1 ^ MUL[slope][t]) for t in range(Q)]
                for bad in ((), (0,), (0, 1, 4, 12)):
                    received = values.copy()
                    for j in bad:
                        received[j] ^= 1 + j
                    assert line_value(received) == values[0]
                    checks += 1
    print(f'GF(16): {checks} line recoveries passed, including errors at the queried point.')


if __name__ == '__main__':
    main()
