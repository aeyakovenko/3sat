"""Exact finite checks for checksum critical clauses and the interior mask law."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import isqrt
from random import Random


def field(q):
    modulus = {4: 0b111, 8: 0b1011, 16: 0b10011}[q]

    def multiply(x, y):
        z = 0
        while y:
            if y & 1:
                z ^= x
            y >>= 1
            x <<= 1
            if x & q:
                x ^= modulus
        return z

    return [[multiply(x, y) for y in range(q)] for x in range(q)]


def row_weights(point, multiplication, v):
    row = [1]
    for p in point:
        row = [multiplication[x][1 ^ p] for x in row] + [
            multiplication[x][p] for x in row]
    return row[:v]


def word_mask(row, lam):
    return sum((((value & lam).bit_count() % 2) << i) for i, value in enumerate(row))


def interior_covariance(q, d, v):
    multiplication = field(q)
    histogram = Counter(word_mask(row_weights(point, multiplication, v), lam)
                        for point in product(range(2, q), repeat=d)
                        for lam in range(1, q))
    n = sum(histogram.values())
    mean = Fraction(-1, q-1)
    for i in range(v):
        observed = sum(count * (-1)**((mask >> i) & 1) for mask, count in histogram.items())
        assert Fraction(observed, n) == mean
    for i, j in product(range(v), repeat=2):
        pair = sum(count * (-1)**(((mask >> i) ^ (mask >> j)) & 1)
                   for mask, count in histogram.items())
        covariance = Fraction(pair, n) - mean**2
        expected = Fraction(q*(q-2), (q-1)**2) * Fraction(-1, q-2)**((i ^ j).bit_count())
        assert covariance == expected
    for center in range(1 << v):
        values = [(Fraction(v-2*(center ^ mask).bit_count(), v), count)
                  for mask, count in histogram.items()]
        avg = sum(value*count for value, count in values) / n
        var = sum((value-avg)**2*count for value, count in values) / n
        assert var <= Fraction(1, v) * (1 + Fraction(1, q-2))**d
    return v*v, 1 << v


def core_checks():
    v, h = 5, 0b10101
    mask_all = (1 << v) - 1
    clauses = [(1 << i, (h ^ (1 << i)) & (1 << i)) for i in range(v)]
    # Represent each disjunction by its two/three pinned falsifying bits.
    for ids in [(0,1), (1,2,3), (0,2,4), (3,4)]:
        support = sum(1 << i for i in ids)
        clauses.append((support, (h ^ support) & support))
    tests = 0
    for chosen in range(1 << len(clauses)):
        constraints = [cl for i, cl in enumerate(clauses) if chosen >> i & 1]
        models = [x for x in range(mask_all+1)
                  if all(x & support != bad for support, bad in constraints)]
        for mask in range(mask_all+1):
            true_bit = (h & mask).bit_count() % 2
            if all((x & mask).bit_count() % 2 == true_bit for x in models):
                assert sum(bool(mask & (1 << i)) for i in range(v)) <= len(constraints)
                tests += 1
    return tests


def projection_and_list_checks():
    rng, mult = Random(71432), field(8)
    tests = 0
    for _ in range(700):
        v = rng.randrange(18, 33)
        point = [rng.randrange(2, 8) for _ in range(5)]
        row = row_weights(point, mult, v)
        distance = min(word_mask(row, lam).bit_count() for lam in range(1, 8))
        touched = set(rng.sample(range(v), rng.randrange(max(1, distance))))
        span = {0}
        for i, value in enumerate(row):
            if i not in touched:
                span |= {z ^ value for z in span}
        if len(touched) < distance:
            assert span == set(range(8))
        candidates = set(rng.sample(range(8), rng.randrange(1, 9)))
        scale = isqrt(len(candidates)-1) + 1
        assert sum(Fraction(int(z in candidates), scale)**2 for z in range(8)) <= 1
        tests += 1
    return tests


def sharp_single_error():
    q, d = 4, 3
    mult = field(q)
    rows = [row_weights(p, mult, 1 << d) for p in product(range(q), repeat=d)]
    for i in range(1 << d):
        collisions = sum(not row[i] for row in rows)
        assert collisions == q**d - (q-1)**d
        wins = sum(not ((row[i] & mask).bit_count() % 2)
                   for row in rows for mask in range(q))
        assert 2*wins == q*(len(rows)+collisions)
    return 1 << d


if __name__ == "__main__":
    cases = [(4,3,7), (8,3,8), (8,3,5), (16,2,4)]
    results = [interior_covariance(*case) for case in cases]
    print(f"{sum(t[0] for t in results)} exact pair covariances; "
          f"{sum(t[1] for t in results)} arbitrary-center variance checks")
    print(f"{core_checks()} wrong-pin subcores; "
          f"{projection_and_list_checks()} adaptive projections and list norms; "
          f"{sharp_single_error()} sharp one-bit errors")
