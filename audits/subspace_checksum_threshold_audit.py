"""Finite checks for local erasure inference from subspace restrictions."""

from fractions import Fraction
from itertools import combinations, product
from math import comb
from random import Random

from checksum_pair_certificates_audit import combination_for_constant
from checksum_selector_distance_audit import BinaryField


def field_dot(field, a, b):
    value = 0
    for x, y in zip(a, b, strict=True):
        value ^= field.mul[x][y]
    return value


def plane_zeros(field):
    """Exhaust all degree-two polynomials, including those with repeated factors."""
    q = field.q
    points = list(product(range(q), repeat=2))
    rows = [(1, x, y, field.mul[x][x], field.mul[x][y], field.mul[y][y]) for x, y in points]
    lines = {sum((field_dot(field, (a, b), pt) == c) << i for i, pt in enumerate(points))
             for a, b in product(range(q), repeat=2) if a or b for c in range(q)}
    counts = [0, 0, 0]
    for coeff in product(range(q), repeat=6):
        if not any(coeff[3:]):
            continue
        zeros = sum((field_dot(field, coeff, row) == 0) << i for i, row in enumerate(rows))
        linear_factors = [line for line in lines if line & zeros == line]
        counts[len(linear_factors)] += 1
        if not linear_factors:
            # Any one zero is a maximal 0-flat, partition at that point
            # using the q+1 lines through it.
            assert zeros.bit_count() <= 1 + (q+1)
        else:
            combined = 0
            for line in linear_factors:
                combined |= line
            assert zeros == combined
    assert all(counts)
    return counts


def arrangement_test(field):
    """Five normals on the moment curve in dimension three."""
    q, d, ell = field.q, 5, 3
    points = list(product(range(q), repeat=3))
    normals = [(1, t, field.mul[t][t]) for t in range(d)]
    hyperplanes = []
    for norm in normals:
        fibers = [0]*q
        for i, point in enumerate(points):
            fibers[field_dot(field, norm, point)] |= 1 << i
        hyperplanes.append(fibers)
    for a, b, c in combinations(hyperplanes, ell):
        assert all((u & v & w).bit_count() == 1 for u, v, w in product(a, b, c))
    upper = sum((-1)**(k+1)*comb(d, k)*q**(ell-k) for k in range(1, ell+1))
    largest = 0
    for offsets in product(range(1, q), repeat=d):
        union = 0
        for axis, shift in enumerate(offsets):
            union |= hyperplanes[axis][shift]
        largest = max(largest, union.bit_count())
    assert largest == upper
    return (q-1)**d, largest, len(points)


def multiply_linear(field, poly, coefficients):
    """Two indeterminates. coefficients are the constant and two linear terms."""
    result = {}
    for (u, v), weight in poly.items():
        for du, dv, c in ((0, 0, coefficients[0]), (1, 0, coefficients[1]), (0, 1, coefficients[2])):
            key = (u+du, v+dv)
            result[key] = result.get(key, 0) ^ field.mul[c][weight]
    return result


def test_top_components(field):
    rng = Random(14259)
    checks = 0
    for _ in range(10):
        matrix = [tuple(rng.randrange(field.q) for _ in range(2)) for _ in range(3)]
        anchor = tuple(rng.randrange(2) for _ in range(3))
        lagrange = []
        for vertex in product(range(2), repeat=3):
            poly = {(0, 0): 1}
            for a, b, r in zip(anchor, vertex, matrix):
                poly = multiply_linear(field, poly, (a ^ b ^ 1, *r))
            lagrange.append(poly)
        top = {(0, 0): 1}
        for row in matrix:
            top = multiply_linear(field, top, (0, *row))
        for table in range(256):
            for i in range(4):
                key = (i, 3-i)
                coeff = 0
                for k, poly in enumerate(lagrange):
                    if table >> k & 1:
                        coeff ^= poly[key]
                assert coeff == (top[key] if table.bit_count() & 1 else 0)
            checks += 1
    return checks


def certificate_tests(field):
    q = field.q
    rng = Random(185476)
    def space():
        matrix = [tuple(rng.randrange(q) for _ in range(2)) for _ in range(2)]
        vals = [(x, y, field.mul[field_dot(field, matrix[0], (x, y))][field_dot(field, matrix[1], (x, y))])
                for x, y in product(range(q), repeat=2) if x or y]
        largest = max(sum(field_dot(field, c, v) == 1 for v in vals)
                      for c in product(range(q), repeat=3))
        rows = []
        for t, mask in product(vals, range(q)):
            row = field.trace[mask]
            for k, z in enumerate(t):
                for i in range(field.s):
                    row |= field.trace[field.mul[field.mul[z][mask]][1 << i]] << (1 + k*field.s+i)
            rows.append(row)
        return Fraction(largest, len(vals)), rows

    checks = 0
    for _ in range(12):
        za, first = space()
        zb, second = space()
        rows = [a ^ (b & 1) ^ ((b & ~1) << (3*field.s)) for a, b in product(first, second)]
        bound = len(rows)*(1+za*zb)/2
        sample = rng.sample(rows, int(bound)+1)
        mask = combination_for_constant(sample)
        assert 0 < mask.bit_count() <= 1+6*field.s
        row = 0
        for i, v in enumerate(sample):
            if mask >> i & 1:
                row ^= v
        assert row == 1
        checks += 1
    return checks


if __name__ == '__main__':
    f4 = BinaryField(4, 0b111)
    f8 = BinaryField(8, 0b1011)
    counts = plane_zeros(f4)
    arrangements, most_zeros, domain = arrangement_test(f8)
    print(f'{sum(counts)} quadratic plane polynomials classified by zero, one or two distinct line factors: {counts}.')
    print(f'{arrangements} affine arrangements checked; maximum {most_zeros}/{domain} attained the order-three bound.')
    print(f'{test_top_components(f4)} multilinear restrictions had the prescribed leading component.')
    print(f'{certificate_tests(f4)} dense samples of witnessed subspace queries recovered the constant.')
