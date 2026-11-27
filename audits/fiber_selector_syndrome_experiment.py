"""Exact audit of trace-polynomial selectors and their centered miss moments."""

from itertools import combinations
from math import comb, gcd
from operator import xor
from functools import reduce

from projective_row_markers_experiment import BinaryField


def field_trace(field, value):
    result = 0
    for _ in range(field.bits):
        result ^= value
        value = field.multiply(value, value)
    assert result in (0, 1)
    return result


def name_syndromes(q, exponents=None):
    """Linear form giving Tr(P(i)) on every coefficient bit of deg(P)<q."""
    field = BinaryField(q - 1)
    if exponents is None:
        exponents = range(q)
    n_names = field.size - 1
    ids = [(1 << length) + payload
           for length in range(q - 1) for payload in range(1 << length)]
    assert ids == list(range(1, n_names + 1))
    syndromes = []
    for i in ids:
        mask = 0
        for j, exponent in enumerate(exponents):
            for bit in range(field.bits):
                weight = field.multiply(1 << bit, field.power(i, exponent))
                mask |= field_trace(field, weight) << (j * field.bits + bit)
        syndromes.append(mask)
    return syndromes


def image_basis(rows, coefficient_bits):
    """Basis of attainable label-evaluation vectors, under uniform seed bits."""
    pivots = {}
    for bit in range(coefficient_bits):
        vector = sum(((row >> bit) & 1) << j for j, row in enumerate(rows))
        while vector:
            key = vector.bit_length() - 1
            if key not in pivots:
                pivots[key] = vector
                break
            vector ^= pivots[key]
    return list(pivots.values())


def check_subsets(rows, degree):
    checks = 0
    for size in range(1, min(degree, len(rows)) + 1):
        for subset in combinations(rows, size):
            assert reduce(xor, subset) != 0
            checks += 1
    return checks


def superset_transform(counts, n, sign):
    """sign=1 computes superset counts, sign=-1 undoes the transform."""
    for j in range(n):
        bit = 1 << j
        for start in range(0, len(counts), 2 * bit):
            for mask in range(start, start + bit):
                counts[mask] += sign * counts[mask | bit]


def miss_histogram(basis, n, trials):
    reachable = [0]
    for generator in basis:
        reachable.extend([mask ^ generator for mask in reachable])
    full = (1 << n) - 1
    histogram = [0] * (n + 1)
    if trials == 1:
        for hit in reachable:
            histogram[(full ^ hit).bit_count()] += 1
    else:
        assert n <= 18
        counts = [0] * (1 << n)
        for hit in reachable:
            counts[full ^ hit] += 1
        superset_transform(counts, n, 1)
        counts = [count**trials for count in counts]
        superset_transform(counts, n, -1)
        assert min(counts) >= 0
        for mask, count in enumerate(counts):
            histogram[mask.bit_count()] += count
    assert sum(histogram) == len(reachable)**trials
    return histogram


def audit(q, fibers, trials):
    names = name_syndromes(q)
    used = [i for fiber in fibers for i in fiber]
    assert len(set(used)) == len(used) and all(fibers)
    max_size = max(map(len, fibers))
    rows = [reduce(xor, (names[i] for i in fiber)) for fiber in fibers]
    degree = q // max_size
    checks = check_subsets(rows, degree)
    basis = image_basis(rows, q * (q-1))
    n = len(fibers)
    histogram = miss_histogram(basis, n, trials)
    denominator = 1 << trials
    samples = sum(histogram)
    for h in range(1, degree // 2 + 1):
        # Scale by denominator^order to keep both expectations integral.
        order = 2 * h
        moment = sum(c * (denominator * j - n)**order for j, c in enumerate(histogram))
        binomial_moment = sum(comb(n, j) * (denominator - 1)**(n - j) *
                              (denominator * j - n)**order for j in range(n + 1))
        assert moment * denominator**n == binomial_moment * samples
        assert moment <= samples * (h + 1) * n**h * (2*h)**(2*h) * denominator**(2*h)
    print(f'q={q} k={max_size} labels={n} selectors={trials} effective seed rank={len(basis)} '
          f'syndrome subsets checked={checks} highest centered moment={2*(degree//2)} '
          f'effective sample tuples={samples}')


def check_progressions(q, width):
    order = (1 << (q - 1)) - 1
    count = 0
    for start in range(order):
        for step in range(1, order):
            if gcd(step, order) != 1:
                continue
            exponents = [(start + j * step) % order for j in range(width)]
            names = name_syndromes(q, exponents)
            count += check_subsets(names, width)
    print(f'q={q} width={width} unit-step progression subset checks={count}')


if __name__ == '__main__':
    audit(4, [(j,) for j in range(7)], 3)
    audit(6, [(j,) for j in range(31)], 1)
    audit(6, [(j,) for j in range(18)], 2)
    audit(6, [(2*j, 2*j+1) for j in range(15)] + [(30,)], 3)
    # Nonconsecutive, unequally sized fibers use a permutation of the names.
    pieces = [(j,) for j in range(5)] + [(j, j+1) for j in range(5,25,2)]
    audit(6, [tuple((7*j+11) % 31 for j in fiber) for fiber in pieces], 2)

    check_progressions(4, 4)
