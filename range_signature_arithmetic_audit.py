"""Finite checks for the signed bucket moment and digit-error bounds."""
from fractions import Fraction
from itertools import combinations, product
from math import gcd, lcm


def moments(errors, buckets=2, p=5):
    # Enumerate the value tuple directly. At up to four distinct sites, it is
    # uniform under the random cubic used in the manuscript.
    means, squares, outcomes = 0, 0, 0
    for slope, intercept in product(range(p), repeat=2):
        loc = [((slope * i + intercept) % p) % buckets for i in range(len(errors))]
        for vals in product(range(p), repeat=len(errors)):
            sums = [0] * buckets
            for j, val in enumerate(vals):
                sign = 0 if val == 0 else (1 if val <= p // 2 else -1)
                sums[loc[j]] += sign * errors[j]
            z = sum(v * v for v in sums)
            means += z
            squares += z * z
            outcomes += 1
    nu = Fraction(p - 1, p)
    mean = Fraction(means, outcomes)
    assert mean == nu * sum(e * e for e in errors)
    variance = Fraction(squares, outcomes) - mean**2
    upper = (nu * (1 - nu) * sum(e**4 for e in errors)
             + 4 * nu**2 * (Fraction(1, buckets) + Fraction(1, p))
             * sum((a * b)**2 for a, b in combinations(errors, 2)))
    assert variance <= upper


def main():
    vectors = [(1,), (1, -1), (0, 3, -3), (2, -1, 4, -5), (0, 0, 0, 0)]
    for vector in vectors:
        moments(vector)
    tested = 0
    for bits in range(1, 97):
        period = 1
        while period < bits:
            period *= 3
        modulus = 3 * period
        residues = [pow(2, i, modulus) for i in range(bits)]
        assert all(residues)
        for a, b in combinations(residues, 2):
            assert (a - b) % modulus and (a + b) % modulus
            tested += 2
    modulus = 1
    for k in range(1, 65):
        modulus = lcm(modulus, k)
        points = [(1, 1, 1), (2, 2, modulus), (3, 1, 1), (4, 4, modulus)]
        true = [sum(w for x, y, w in points if x <= a and y <= b)
                for a, b in ((2, 3), (3, 2))]
        claims = [2 * modulus + 1, 2]
        errors = [claim - actual for claim, actual in zip(claims, true)]
        assert sum(errors) == 0 and gcd(*errors) == modulus
        assert all(e % m == 0 for m in range(1, k + 1) for e in errors)
        assert all(0 <= v <= sum(w for _, _, w in points) for v in claims)
    print(f"Passed {len(vectors)} exact bucket moment checks and {tested} signed digit pairs, and 64 exact residue escapes.")


if __name__ == "__main__":
    main()
