"""Finite audits for affine rank-promised product reductions and fixed-answer ranks."""

from itertools import product
from math import prod
from random import Random


def insert(basis, word):
    while word:
        pivot = word.bit_length() - 1
        if pivot not in basis:
            basis[pivot] = word
            return True
        word ^= basis[pivot]
    return False


def independent(words):
    basis = {}
    return [word for word in words if insert(basis, word)]


def parity(word):
    return word.bit_count() % 2


def apply(rows, word):
    return sum(parity(row & word) << j for j, row in enumerate(rows))


def columns_as_rows(columns, d):
    return [sum((col >> j & 1) << k for k, col in enumerate(columns)) for j in range(d)]


def rectangular_classification(a, b, c):
    """Dimension of quadratic polynomials vanishing on true product graphs."""
    variables = a * b + b * c + a * c
    basis = {}
    for left in product(range(1 << b), repeat=a):
        for right in product(range(1 << b), repeat=c):
            outputs = [parity(x & y) for x in left for y in right]
            bits = [v >> j & 1 for v in left + right for j in range(b)] + outputs
            active = [i for i, bit in enumerate(bits) if bit]
            evaluation = 1
            for i in active:
                evaluation |= 1 << (1 + i)
            for index, i in enumerate(active):
                for j in active[:index]:
                    evaluation |= 1 << (1 + variables + i * (i - 1) // 2 + j)
            insert(basis, evaluation)
    dimension = 1 + variables + variables * (variables - 1) // 2
    assert dimension - len(basis) == a * c


def subspace_count(d, k):
    return prod((1 << d) - (1 << i) for i in range(k)) // prod(
        (1 << k) - (1 << i) for i in range(k)
    )


def fixed_target(d, rank):
    """Independently generate the predicates, types, zeta incidences and binary rank."""
    vectors = range(1 << d)
    maps = [tuple(apply(rows, x) for x in vectors) for rows in product(vectors, repeat=d)]
    target = tuple(x & ((1 << rank) - 1) for x in vectors)
    image = set(target)
    rows = [
        frozenset((x, y) for x, y in enumerate(f) if y in image)
        if image <= set(f) else None
        for f in maps
    ]
    columns = []
    for g in maps:
        graph = frozenset(zip(g, target))
        columns.append(graph if len(graph) == len(set(g)) else None)
    types = set(rows) - {None}
    assert types == set(columns) - {None}
    expected = sum(subspace_count(d, k) * prod((1 << k) - (1 << i) for i in range(rank))
                   for k in range(rank, d + 1))
    assert len(types) == expected
    binary_rows = []
    for f, row in zip(maps, rows):
        word = 0
        for j, (g, column) in enumerate(zip(maps, columns)):
            direct = all(f[y] == value for y, value in zip(g, target))
            incidence = row is not None and column is not None and column <= row
            assert direct == incidence
            if direct:
                word |= 1 << j
        binary_rows.append(word)
    assert len(independent(binary_rows)) == expected
    return expected


def orthogonal(vectors, masks):
    return independent(x for x in vectors if all(parity(x & y) == 0 for y in masks))


def embedded_product(d, q, s, rng):
    masks = [tuple([rng.randrange(1 << d) for _ in range(d)] for _ in range(3))
             for _ in range(q)]
    vectors = range(1 << d)
    left = [1 << i for i in range(s)]
    right_masks = [apply(columns_as_rows(w, d), l) for _, _, w in masks for l in left]
    right = orthogonal(vectors, right_masks)[:s]
    assert len(right) == s
    h_masks = [apply(columns_as_rows(u, d), l) for u, _, _ in masks for l in left]
    g_masks = [apply(v, z) for _, v, _ in masks for z in right]
    h = orthogonal(vectors, h_masks)
    g = orthogonal(vectors, g_masks)
    gram = [apply(g, x) for x in h]
    assert len(independent(gram)) >= d - 2 * q * s
    assert all(parity(x & y) == 0 for x in right_masks for y in right)


def row_block_counts(d, r):
    """Check the exact formulas by actually partitioning the operand slots."""
    groups = [range(j, min(j + r, d)) for j in range(0, d, r)]
    sizes = [sum(1 for _ in product(rows, range(d))) + d * d for rows in groups]
    expected = d * d + ((d + r - 1) // r) * d * d
    assert sum(sizes) == expected
    if d % r == 0:
        assert expected == d * d + d ** 3 // r


def main():
    for sizes in [(1, 2, 1), (1, 3, 2), (2, 2, 1), (2, 2, 2), (2, 3, 2)]:
        rectangular_classification(*sizes)
    for d in range(2, 21):
        for r in range(1, d + 1):
            row_block_counts(d, r)
    rng = Random(74153)
    for d in range(5, 11):
        for q in range(1, 4):
            for s in range(1, d + 1):
                if d - 2 * q * s >= 2 and s <= d - q * s:
                    for _ in range(4):
                        embedded_product(d, q, s, rng)
    for d in range(1, 4):
        ranks = [fixed_target(d, r) for r in range(d + 1)]
        print(f"fixed-target ranks at d={d}: {ranks}")
    print("rectangular classification, row-block slot and paired-embedding checks passed")


if __name__ == "__main__":
    main()
