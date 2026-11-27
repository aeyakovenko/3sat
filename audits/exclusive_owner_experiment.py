"""Exhaustive independent group laws on {0,1,2}, in quarter increments."""

from fractions import Fraction
from itertools import combinations_with_replacement
from math import prod


def main():
    laws = [(z, o, 4-z-o) for z in range(5) for o in range(5-z)]
    tested = majority = 0
    worst = Fraction(0)
    for groups in range(1, 5):
        scale = 4 ** groups
        for model in combinations_with_replacement(laws, groups):
            weights = [one * prod(other[0] for j, other in enumerate(model) if j != i)
                       for i, (_, one, _) in enumerate(model)]
            success = sum(weights)
            q = Fraction(scale - success, scale)
            gamma = Fraction(scale - max(weights), scale)
            assert q <= gamma <= 2*q
            if 2*success > scale:
                candidates = [i for i, (zero, one, _) in enumerate(model)
                              if one*scale >= 4*success and zero < 2]
                assert len(candidates) == 1
                owner = candidates[0]
                others_zero = prod(v[0] for j, v in enumerate(model) if j != owner)
                assert 4 * others_zero >= success
                assert gamma <= q + q*q
                majority += 1
            if q:
                worst = max(worst, gamma / q)
            tested += 1
    print(f'{tested} group laws; {majority} strict singletons; max Γ/q = {worst}')


def field_multiply(a, b, order, modulus):
    product = 0
    while b:
        if b & 1:
            product ^= a
        b >>= 1
        a <<= 1
        if a & order:
            a ^= modulus
    return product


def check_affine_models():
    for order, modulus in [(4, 0b111), (8, 0b1011), (16, 0b10011)]:
        rows = [[field_multiply(a, p, order, modulus) ^ b for p in range(1, order)]
                for a in range(order) for b in range(order)]
        for i in range(order - 1):
            for j in range(i):
                assert len({(row[i], row[j]) for row in rows}) == order * order
        anomalies = sum(row.count(x) != 1 for row in rows for x in range(order))
        collisions = sum(row.count(x) * (row.count(x) - 1) for row in rows for x in range(order))
        assert anomalies == order * (2 * order - 1)
        assert collisions == order * (order - 1) * (order - 2)
    print('Affine counterexamples passed at field orders 4, 8 and 16')


if __name__ == '__main__':
    main()
    check_affine_models()
