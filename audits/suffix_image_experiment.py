"""Enumerate small hidden-coefficient maps and minimum parity certificates."""

from collections import Counter
from itertools import combinations, product


def parity(value):
    return value.bit_count() % 2


def affine(code, suffix):
    return (code & 1) ^ parity((code >> 1) & suffix)


def test_hidden_coefficients():
    # The two quadratics have exactly one disjoint pair covering four bits.
    cases = 0
    for a, b in product(range(32), repeat=2):
        fibers = Counter()
        for x in range(16):
            x0, x1, x2, x3 = ((x >> i) & 1 for i in range(4))
            f = (x0 & x1) ^ (x0 & x2) ^ affine(a, x)
            g = (x2 & x3) ^ (x1 & x2) ^ affine(b, x)
            fibers[(f, g)] += 1
        assert len(fibers) == 4 and all(count % 2 for count in fibers.values())
        cases += 1
    return cases


def test_certificates():
    vectors = range(1, 8)
    cases = 0
    for size in range(1, 8):
        maximum = 0
        for family in combinations(vectors, size):
            def separates(masks):
                return all(any(parity(mask & v) for mask in masks) for v in family)

            width = next(k for k in range(1, 4)
                         if any(separates(masks) for masks in combinations(vectors, k)))
            maximum = max(maximum, width)
            cases += 1
        assert maximum == (size + 1).bit_length() - 1
    return cases


if __name__ == "__main__":
    print(f"Checked {test_hidden_coefficients()} hidden affine perturbations")
    print(f"Checked {test_certificates()} families of nonzero hit vectors")
