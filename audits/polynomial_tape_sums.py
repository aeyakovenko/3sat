"""Check coset sums of polynomial oracles over GF(16) as Reed–Solomon words."""

from fractions import Fraction
from itertools import product
from math import comb


def multiply(x, y):
    out = 0
    while y:
        if y & 1:
            out ^= x
        x <<= 1
        if x & 16:
            x ^= 0b10011  # X^4 + X + 1
        y >>= 1
    return out


MUL = [[multiply(x, y) for y in range(16)] for x in range(16)]
INV = [0] + [MUL[x].index(1) for x in range(1, 16)]


def power(x, exponent):
    acc = 1
    for _ in range(exponent):
        acc = MUL[acc][x]
    return acc


def field_sum(words):
    result = 0
    for word in words:
        result ^= word
    return result


def field_product(words):
    result = 1
    for word in words:
        result = MUL[result][word]
    return result


def rank(rows):
    pivots = {}
    for candidate in rows:
        row = list(candidate)
        for j, value in enumerate(row):
            if not value:
                continue
            if j not in pivots:
                pivots[j] = [MUL[INV[value]][x] for x in row]
                break
            previous = pivots[j]
            for k in range(j, len(row)):
                row[k] ^= MUL[value][previous[k]]
    return len(pivots)


def all_subspaces():
    zero = frozenset({0})
    seen = {zero}
    pending = [zero]
    while pending:
        subspace = pending.pop()
        for a in range(1, 16):
            if a in subspace:
                continue
            larger = subspace | {x ^ a for x in subspace}
            if larger not in seen:
                seen.add(larger)
                pending.append(larger)
    return sorted(seen, key=lambda space: (len(space), tuple(sorted(space))))


def check_subspace(subspace, max_degree_bound):
    q = len(subspace)
    cosets = sorted({tuple(sorted(a ^ u for u in subspace)) for a in range(16)})
    locators = [field_product(coset) for coset in cosets]
    assert len(set(locators)) == len(cosets) == 16 // q
    derivative = field_product(u for u in subspace if u)

    # Sum of a coset's powers below q vanishes except in degree q-1.
    monomial_sums = []
    for degree in range(max_degree_bound):
        row = [field_sum(power(x, degree) for x in coset) for coset in cosets]
        if degree < q:
            expected = derivative if degree == q - 1 else 0
            assert row == [expected] * len(cosets)
        monomial_sums.append(row)

    # Compare exact field spans using the rank of the stacked generating sets.
    for h in range(max_degree_bound + 1):
        dimension = min(h // q, len(cosets))
        rs_rows = [[power(a, i) for a in locators] for i in range(dimension)]
        image = monomial_sums[:h]
        assert rank(image) == rank(rs_rows) == rank(image + rs_rows) == dimension


def check_radius_one():
    hits = 0
    for word in product(range(16), repeat=4):
        hits += any(word.count(c) >= 3 for c in set(word))
    assert hits == 16 * (1 + 4 * 15) == 976
    return hits, Fraction(hits, 16 ** 4)


def check_length_eight_lines():
    # Eight cosets of U={0,1} use distinct, usually nonconsecutive RS locators.
    locators = sorted({MUL[a][a ^ 1] for a in range(16)})
    lines = {tuple(intercept ^ MUL[slope][a] for a in locators)
             for intercept, slope in product(range(16), repeat=2)}
    assert len(locators) == 8 and len(lines) == 256
    # The code is linear, so distances from zero determine minimum distance.
    minimum = min(sum(x != 0 for x in line) for line in lines if any(line))
    assert minimum == 7
    radius_three_count = len(lines) * sum(comb(8, j) * 15 ** j for j in range(4))
    return minimum, radius_three_count


if __name__ == '__main__':
    spaces = all_subspaces()
    assert [sum(len(space) == 2 ** i for space in spaces) for i in range(5)] == [1, 15, 35, 15, 1]
    for space in spaces:
        check_subspace(space, 20)
    hits, probability = check_radius_one()
    distance, ball_count = check_length_eight_lines()
    print(f'{len(spaces)} subspaces and 21 degree bounds, all {len(spaces)*21} image spans verified')
    print(f'Length four, within one of a constant: {hits}/65536 = {probability}')
    print(f'Length eight, 256 lines: minimum distance {distance}, disjoint radius-three balls cover {ball_count} words')
