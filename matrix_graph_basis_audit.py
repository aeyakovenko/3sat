"""Exhaust binary matrix graph, phase and disjointness conversions at sides 1 and 2."""

from itertools import product


def entry(matrix, n, row, col):
    return (matrix >> (row * n + col)) & 1


def pack(rows):
    n = len(rows)
    return sum(bit << (i * n + j) for i, row in enumerate(rows)
               for j, bit in enumerate(row))


def matmul(a, b, n):
    return pack([[sum(entry(a, n, i, k) * entry(b, n, k, j)
                      for k in range(n)) % 2
                  for j in range(n)] for i in range(n)])


def trilinear_bit(a, b, z, n):
    return sum(entry(a, n, i, k) * entry(b, n, k, j) * entry(z, n, i, j)
               for i, k, j in product(range(n), repeat=3)) % 2


def add_diagonal_bit(matrix, n, last):
    rows = [[entry(matrix, n, i, j) for j in range(n)] + [0]
            for i in range(n)]
    return pack(rows + [[0] * n + [last]])


def local_transform(values, matrix, p):
    """Apply a two-by-two matrix independently on every bit of the index."""
    values = list(values)
    stride = 1
    while stride < len(values):
        for start in range(0, len(values), 2 * stride):
            for left in range(start, start + stride):
                right = left + stride
                x, y = values[left], values[right]
                values[left] = (matrix[0][0] * x + matrix[0][1] * y) % p
                values[right] = (matrix[1][0] * x + matrix[1][1] * y) % p
        stride *= 2
    return values


def double_operands(a, b, n):
    size = 2 * n
    # Top rows carry [A | 1 | 0]. The extra summand complements the second copy.
    left = [[0] * size for _ in range(size)]
    right = [[0] * size for _ in range(size)]
    for i in range(n):
        left[i][:n] = [entry(a, n, i, j) for j in range(n)]
        left[i][n] = 1
        row = [entry(b, n, i, j) for j in range(n)]
        right[i] = row + row
    right[n][n:] = [1] * n
    return pack(left), pack(right)


def double_mask(c, n):
    rows = []
    for i in range(n):
        row = [entry(c, n, i, j) for j in range(n)]
        rows.append([1 - bit for bit in row] + row)
    return pack(rows + [[0] * (2 * n) for _ in range(n)])


def audit(n):
    count = 1 << (n * n)
    walsh = ((1, 1), (1, -1))
    disjoint = ((1, 1), (1, 0))
    inverse = ((0, 1), (1, -1))
    enlarged = [[add_diagonal_bit(c, n, t) for t in range(2)] for c in range(count)]
    masks = [double_mask(c, n) for c in range(count)]
    for a, b in product(range(count), repeat=2):
        ab = matmul(a, b, n)
        graph = [int(c == ab) for c in range(count)]
        phases = [(-1) ** ((ab & z).bit_count() % 2) for z in range(count)]
        zero_on_mask = [int((ab & z) == 0) for z in range(count)]
        for p in (3, 5, 7):
            expected = [value % p for value in phases]
            assert local_transform(graph, walsh, p) == expected
            inverse_walsh = local_transform(expected, walsh, p)
            assert [(x * pow(count, -1, p)) % p for x in inverse_walsh] == graph
        for p in (2, 3, 5):
            assert local_transform(graph, disjoint, p) == zero_on_mask
            assert local_transform(zero_on_mask, inverse, p) == graph
        a2, b2 = double_operands(a, b, n)
        ab2 = matmul(a2, b2, 2 * n)
        for i, j in product(range(2 * n), repeat=2):
            expected_bit = (entry(ab, n, i, j % n) ^ (j >= n)) if i < n else 0
            assert entry(ab2, 2 * n, i, j) == expected_bit
        for z in range(count):
            assert int((ab2 & masks[z]) == 0) == graph[z]
            bit = trilinear_bit(a, b, z, n)
            vals = [trilinear_bit(enlarged[a][1], enlarged[b][1],
                                  enlarged[z][t], n + 1) for t in range(2)]
            assert vals == [bit, bit ^ 1]
            assert vals[1] - vals[0] == phases[z]
    return count ** 3


def binary_rank(matrix, n):
    """Dimension via exhaustive XOR-span growth, independently of feature elimination."""
    span = {0}
    for i in range(n):
        row = (matrix >> (i * n)) % (1 << n)
        span |= {v ^ row for v in span}
    return len(span).bit_length() - 1


def reduce_column(column, basis):
    while column:
        pivot = column.bit_length() - 1
        if pivot not in basis:
            break
        column ^= basis[pivot]
    return column


def minimum_zero_indicator_degree(rows, n, monomials):
    # Bit j of a truth-table column is its value at the j-th promised matrix.
    assert rows[0] == 0
    target = 1
    basis = {}
    for degree, supports in enumerate(monomials):
        for support in supports:
            column = sum(1 << j for j, matrix in enumerate(rows)
                         if (matrix & support) == support)
            column = reduce_column(column, basis)
            if column:
                basis[column.bit_length() - 1] = column
        if reduce_column(target, basis) == 0:
            return degree
    raise AssertionError(f"degree {n*n} did not interpolate a function")


def audit_promised_degrees(n):
    matrices = list(range(1 << (n * n)))
    rank = [binary_rank(m, n) for m in matrices]
    monomials = [[mask for mask in matrices if mask.bit_count() == k]
                 for k in range(n * n + 1)]
    tested = 0
    for r in range(n + 1):
        for s in range(n * n + 1):
            rows = [m for m in matrices if rank[m] <= r and m.bit_count() <= s]
            degree = minimum_zero_indicator_degree(rows, n, monomials)
            expected = min(n * r, s)
            assert degree == expected, (n, r, s, degree, expected)
            tested += 1
    return tested


if __name__ == "__main__":
    for side in (1, 2):
        triples = audit(side)
        print(f"d={side}: verified Walsh, disjointness, folded scalar and mask projection "
              f"on all {triples} triples")
    for side in (1, 2, 3):
        count = audit_promised_degrees(side)
        print(f"d={side}: minimum degree equals min(d*r,s) at all {count} promises")
