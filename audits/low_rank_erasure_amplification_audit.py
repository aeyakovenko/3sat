"""Exact finite tests for rank-one smoothing and four certified product queries.

Matrices are row-major integers. Every probability calculation uses counts
of equally likely outcomes; decimal numbers are only used for display.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import prod


def parity(x):
    return x.bit_count() % 2


def outer(u, v, n):
    return sum(v << (i*n) for i in range(n) if u >> i & 1)


def rows(x, n):
    return [(x >> (i*n)) & ((1 << n)-1) for i in range(n)]


def matvec(x, v, n):
    return sum(parity(row & v) << i for i, row in enumerate(rows(x, n)))


def vecmat(v, x, n):
    result = 0
    for i, row in enumerate(rows(x, n)):
        if v >> i & 1:
            result ^= row
    return result


@lru_cache(maxsize=None)
def multiply(a, b, n):
    return sum(vecmat(row, b, n) << (i*n) for i, row in enumerate(rows(a, n)))


def rank(mat, n):
    space = {0}
    for row in rows(mat, n):
        space |= {x ^ row for x in space}
    return len(space).bit_length()-1


def walk(n, k):
    step = Counter(outer(u, v, n) for u, v in product(range(1 << n), repeat=2))
    counts = {0: 1}
    for _ in range(k):
        updated = Counter()
        for a, x in counts.items():
            for b, y in step.items():
                updated[a ^ b] += x*y
        counts = updated
    return counts


def spectrum():
    characters = joint = 0
    for n in (1, 2, 3):
        for k in (1, 2, 3):
            steps = walk(n, k)
            size = sum(steps.values())
            mats = range(1 << (n*n))
            for char in mats:
                numerator = sum((-1)**parity(char & x) * count for x, count in steps.items())
                assert numerator * 2**(k * rank(char, n)) == size
                characters += 1
            if n == 2:
                for a, b in product(mats, repeat=2):
                    num = sum((-1)**(parity(a & x) ^ parity(b & y))*p*q
                              for x, p in steps.items() for y, q in steps.items())
                    assert num * 2**(k*(rank(a, n)+rank(b, n))) == size**2
                    joint += 1
    return characters, joint


def corrections():
    n = 2
    mats = range(1 << (n*n))
    checked = 0
    # Explicitly write an arbitrary shift as a sum of n rank-one row matrices.
    for a, b, l, m in product(mats, repeat=4):
        correction = 0
        for i, row in enumerate(rows(l, n)):
            correction ^= outer(1 << i, vecmat(row, b ^ m, n), n)
        for i, row in enumerate(rows(m, n)):
            correction ^= outer(matvec(a, 1 << i, n), row, n)
        assert multiply(a ^ l, b ^ m, n) ^ correction == multiply(a, b, n)
        checked += 1
    masks = 0
    for a, b, x, y in product(mats, repeat=4):
        assert (multiply(x, y, n) ^ multiply(a ^ x, y, n) ^ multiply(x, b ^ y, n)
                ^ multiply(a ^ x, b ^ y, n)) == multiply(a, b, n)
        masks += 1
    return checked, masks


def shifted_matrix(a, di, dj, n):
    result = 0
    for i, j in product(range(n), repeat=2):
        if a >> (i*n+j) & 1:
            result |= 1 << (((i+di) % n)*n + (j+dj) % n)
    return result


def biased_oracle(a, b, i, j):
    # Withholds all odd-parity factors and only reports position (0,0).
    if (i, j) != (0, 0) or parity(a) or parity(b):
        return None
    return multiply(a, b, 2) & 1


def symmetrized_counts():
    table = []
    for i, j in product(range(2), repeat=2):
        f = []
        for a, b in product(range(16), repeat=2):
            hits = 0
            for di, dj in product(range(2), repeat=2):
                answer = biased_oracle(shifted_matrix(a, di, 0, 2), shifted_matrix(b, 0, dj, 2),
                                       (i+di) % 2, (j+dj) % 2)
                if answer is not None:
                    assert answer == (multiply(a, b, 2) >> (2*i+j) & 1)
                    hits += 1
            f.append(hits)
        table.append(f)
    assert all(f == table[0] for f in table)
    return table[0], 4


def convolve_pair(f, counts):
    # Both operand masks are independent. Two 1-D convolutions implement the
    # full joint update without treating the pair as a single rank-one matrix.
    left = [sum(w*f[(a ^ u)*16 + b] for u, w in counts.items())
            for a, b in product(range(16), repeat=2)]
    return [sum(w*left[a*16 + (b ^ u)] for u, w in counts.items())
            for a, b in product(range(16), repeat=2)]


def extreme_four_product_coverage(hit, denom):
    # The four uniform-masked factor pairs are correlated. Condition on both
    # masks first; only the four oracle searches have independent randomness.
    distinct = sorted(set(hit))
    ids = [distinct.index(z) for z in hit]

    @lru_cache(maxsize=None)
    def combined(factors):
        return prod(distinct[i] for i in factors)

    all_values = []
    for a, b in product(range(16), repeat=2):
        counts = Counter(tuple(sorted((ids[x*16+y], ids[(a ^ x)*16+y],
                                       ids[x*16+(b ^ y)], ids[(a ^ x)*16+(b ^ y)])))
                         for x, y in product(range(16), repeat=2))
        all_values.append(sum(frequency*combined(key) for key, frequency in counts.items()))
    return tuple(Fraction(x, 256 * denom**4) for x in (min(all_values), max(all_values)))


def erasure():
    f, pieces = symmetrized_counts()
    density = Fraction(sum(f), len(f)*pieces)
    assert density == Fraction(1, 16)
    # Even repeated cyclic shifts cannot cover odd-factor targets with the
    # four-product identity unless the factors themselves are perturbed.
    plain = extreme_four_product_coverage([int(x > 0) for x in f], 1)
    assert plain[0] == 0

    k, attempts = 5, 64
    shifts = walk(2, k)
    smoothed = convolve_pair(f, shifts)
    denom = pieces * sum(shifts.values())**2
    excess_variance = sum((Fraction(x, denom)-density)**2 for x in smoothed)/len(f)
    assert excess_variance <= density*(1-density)/2**(2*k)
    bad = Fraction(sum(2*x < density*denom for x in smoothed), len(f))
    assert bad <= 4*(1-density)/(2**(2*k)*density)
    success = [denom**attempts - (denom-x)**attempts for x in smoothed]
    independent = extreme_four_product_coverage(success, denom**attempts)
    assert independent[0] > Fraction(1, 2)

    # The related stationary-walk variant pays only for one outer product
    # per operand at each step. Conditional per-state misses are propagated
    # exactly, with fresh cyclic shifts of the reported coordinate per query.
    length = 96
    step = walk(2, 1)
    mass, scale = [1]*len(f), 1
    for t in range(1, length+1):
        if t == 1:
            mass, scale = [pieces-v for v in f], pieces
        else:
            mass = [x*(pieces-v) for x, v in zip(convolve_pair(mass, step), f)]
            scale *= sum(step.values())**2 * pieces
    stationary_miss = Fraction(sum(mass), len(f)*scale)
    assert stationary_miss <= (1-density)*(1-density/2)**(length-1)
    sequential = extreme_four_product_coverage([scale-x for x in mass], scale)
    assert sequential[0] >= 1 - 4*stationary_miss
    assert sequential[0] > Fraction(1, 2)
    return density, plain, independent, sequential


if __name__ == '__main__':
    eigen, joint = spectrum()
    repaired, masked = corrections()
    density, plain, smoothed, sequential = erasure()
    print(f'{eigen} single-operand and {joint} paired eigenvalues; {repaired} '
          f'low-rank corrections and {masked} four-product identities')
    print(f'erasure density {density}, unsmoothed worst {float(plain[0]):.6f}, '
          f'5-rank/64-try worst {float(smoothed[0]):.6f}, '
          f'96-step walk worst {float(sequential[0]):.6f}, all 256 factor pairs')
