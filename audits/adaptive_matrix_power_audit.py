"""Exhaust small binary matrix powers via determinant covers and shared weights."""
from itertools import permutations
from math import lcm
from random import Random


def pmul(a, b):
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        b >>= 1
    return value


def prem(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def pgcd(a, b):
    while b:
        a, b = b, prem(a, b)
    return a


def ppow(a, exponent, modulus):
    result = prem(1, modulus)
    while exponent:
        if exponent & 1:
            result = prem(pmul(result, a), modulus)
        a = prem(pmul(a, a), modulus)
        exponent >>= 1
    return result


def factor_period(chi, d):
    image = prem(2, chi)
    counts = [0] * (d + 1)
    odd = 1
    for j in range(1, d + 1):
        image = prem(pmul(image, image), chi)
        total = pgcd(image ^ 2, chi).bit_length() - 1
        counts[j] = total - sum(counts[i] for i in range(1, j) if j % i == 0)
        assert counts[j] >= 0 and counts[j] % j == 0
        if counts[j]:
            odd *= (1 << j) - 1
    assert sum(counts) <= d
    period = odd << d.bit_length()
    nil = ppow(2, d, chi)
    assert prem(pmul(nil, ppow(2, period, chi) ^ 1), chi) == 0
    return period


def cover(matrix, rows, cols):
    # Expand each fixed row-column pair into the diagonal-one or z*A entry.
    coef = 0
    for image in permutations(cols):
        term = 1
        for row, col in zip(rows, image):
            entry = int(row == col) | ((matrix[row] >> col & 1) << 1)
            term = pmul(term, entry)
        coef ^= term
    return coef


def shared_weights(d, denominator, k, chi):
    early = [1]
    for n in range(1, 2 * d):
        b = 0
        for j in range(1, min(d, n) + 1):
            if denominator >> j & 1:
                b ^= early[n-j]
        early.append(b)
    if k < d:
        return sum(early[k-j] << j for j in range(k+1))
    residue = ppow(2, k-d+1, chi)
    weights = 0
    for j in range(d):
        value = 0
        for h in range(d):
            if residue >> h & 1:
                value ^= early[d-1-j+h]
        weights |= value << j
    return weights


def matrix_mul(left, right):
    def row_product(row):
        value = 0
        for j, r in enumerate(right):
            if row >> j & 1:
                value ^= r
        return value
    return tuple(row_product(row) for row in left)


def matrix_power(matrix, exponent):
    result = tuple(1 << j for j in range(len(matrix)))
    while exponent:
        if exponent & 1:
            result = matrix_mul(result, matrix)
        matrix = matrix_mul(matrix, matrix)
        exponent >>= 1
    return result


def check_matrix(matrix, exponents):
    d = len(matrix)
    indices = tuple(range(d))
    denominator = cover(matrix, indices, indices)
    chi = sum(((denominator >> j) & 1) << (d-j) for j in range(d+1))
    numerators = [[cover(matrix, [k for k in indices if k != j],
                         [k for k in indices if k != i]) for j in indices] for i in indices]
    period = factor_period(chi, d)
    entries = transcripts = 0
    for k in exponents:
        reduced = k if k < d else d + (k-d) % period
        weights = shared_weights(d, denominator, reduced, chi)
        expected = matrix_power(matrix, k)
        claimed = tuple(sum(((num & weights).bit_count() % 2) << j
                            for j, num in enumerate(row)) for row in numerators)
        assert claimed == expected
        entries += d*d
        for seed in indices:
            i = j = seed
            for step in range(d):
                actual = (expected[i] >> j) & 1
                via_cofactor = (numerators[i][j] & weights).bit_count() % 2
                assert actual == via_cofactor
                i, j = (i+j+actual) % d, (step+2*j+actual) % d
            transcripts += 1
    return entries, transcripts


def label_counts(d):
    initial = tuple(1 << j for j in range(d))
    longest_tail = largest_orbit = 0
    common_period = 1
    for code in range(1 << (d*d)):
        matrix = tuple((code >> (i*d)) & ((1 << d)-1) for i in range(d))
        seen = {}
        state = initial
        while state not in seen:
            seen[state] = len(seen)
            state = matrix_mul(state, matrix)
        longest_tail = max(longest_tail, seen[state])
        common_period = lcm(common_period, len(seen)-seen[state])
        largest_orbit = max(largest_orbit, len(seen))
    odd = lcm(*((1 << j)-1 for j in range(1, d+1)))
    assert longest_tail == d
    assert common_period == odd << ((d-1).bit_length())
    assert largest_orbit == (2 if d == 1 else (1 << d)-1)
    return longest_tail + common_period, largest_orbit


def sparse_diagonal_catalog(d):
    identity = tuple(1 << i for i in range(d))
    nil = tuple(0 if i == 0 else 1 << (i-1) for i in range(d))
    base = [nil, tuple(x ^ y for x, y in zip(nil, identity))]
    for e in range(1, d+1):
        period = (1 << e)-1
        p = next(p for p in range(1 << e, 2 << e)
                 if {ppow(2, j, p) for j in range(1, period+1)} == set(range(1, period+1)))
        rows = list(identity)
        for i in range(e):
            rows[i] = (0 if i == 0 else 1 << (i-1)) | ((p >> i & 1) << (e-1))
        base.append(tuple(rows))
    catalog = set()
    for matrix in base:
        for i in range(d):
            perm = list(identity)
            perm[0], perm[i] = perm[i], perm[0]
            for j in range(d):
                trans = list(identity)
                if j != i:
                    trans[j] ^= 1 << i
                transformed = matrix_mul(perm, matrix_mul(trans, matrix_mul(matrix, matrix_mul(trans, perm))))
                assert sum(x.bit_count() for x in transformed) <= 5*d
                catalog.add(transformed)
    return catalog


def diagonal_label_count(d, count):
    signatures = [0] * (count+3)
    for m, a in enumerate(sparse_diagonal_catalog(d)):
        v = 1
        for k in range(count+3):
            signatures[k] |= (v & 1) << m
            v = sum(((row & v).bit_count() & 1) << i for i, row in enumerate(a))
    assert len(set(signatures)) == count
    assert signatures[count:] == signatures[d:d+3]


def main():
    labels = [label_counts(d) for d in range(1, 5)]
    for d, (total, _) in enumerate(labels, 1):
        diagonal_label_count(d, total)
    print("Before/after-matrix label optima:", labels, "sparse fixed diagonals verified")
    polys = 0
    for d in range(1, 10):
        for p in range(1 << d, 2 << d):
            factor_period(p, d)
            polys += 1
    matrices = entries = transcripts = 0
    rng = Random(79283)
    for d in range(1, 5):
        codes = range(1 << (d*d)) if d <= 3 else rng.sample(range(1 << 16), 30)
        exponents = list(range(2*d+3)) + [29, 107, 0x32124557, (1 << 150) + 17013]
        for code in codes:
            a = tuple((code >> (i*d)) & ((1 << d)-1) for i in range(d))
            e, t = check_matrix(a, exponents)
            matrices += 1
            entries += e
            transcripts += t
    print(f"{polys} characteristic-polynomial period tests, {matrices} matrices")
    print(f"{entries} direct power entries and {transcripts} adaptive transcripts agreed")


if __name__ == "__main__":
    main()
