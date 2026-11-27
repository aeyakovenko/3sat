"""Check row projections, Laurent slices, and the two forced-weight constructions."""

from itertools import product
from math import comb
import random


def lerp_coefficient(points, values, degree, prime):
    answer = 0
    for point, value in zip(points, values):
        numerator = [1]
        denominator = 1
        for other in points:
            if other == point:
                continue
            expanded = [0] * (len(numerator) + 1)
            for j, coeff in enumerate(numerator):
                expanded[j] -= other * coeff
                expanded[j + 1] += coeff
            numerator = [entry % prime for entry in expanded]
            denominator = denominator * (point - other) % prime
        answer += value * numerator[degree] * pow(denominator, -1, prime)
    return answer % prime


def convolution(left, right, m, prime):
    return [sum(left[j] * right[k - j] for j in range(k + 1)) % prime
            for k in range(m + 1)]


def series(value, m, prime, squared):
    base = [1, value] + [0] * (m - 1)
    if not squared:
        return base
    root = [1]
    for k in range(1, m + 1):
        middle = sum(root[j] * root[k - j] for j in range(1, k))
        root.append((base[k] - middle) * pow(2, -1, prime) % prime)
    return convolution(root, root, m, prime)


def check_slices(m, prime, rng):
    maps = list(product(range(m), repeat=m))
    patterns = list(product((False, True), repeat=m))
    table = {}
    for mapping in maps:
        weights = [rng.randrange(prime) for _ in patterns]
        weights[0] = (int(len(set(mapping)) == m) - sum(weights[1:])) % prime
        table[mapping] = weights
    x = [[rng.randrange(prime) for _ in range(m)] for _ in range(m)]
    columns = []
    for k, pattern in enumerate(patterns):
        points = list(range(1, 4 * m + 2))
        values = []
        for point in points:
            total = 0
            for mapping, weights in table.items():
                arguments = [(point if doubled else pow(point, -1, prime)) * x[i][column]
                             for i, (column, doubled) in enumerate(zip(mapping, pattern))]
                for powers, coeff in zip(patterns, weights):
                    term = coeff
                    for value, high in zip(arguments, powers):
                        term = term * pow(value, 1 + high, prime) % prime
                    total += term
            values.append(total * pow(point, 2 * m, prime) % prime)
        extracted = lerp_coefficient(points, values, m + 3 * sum(pattern), prime)
        expected = 0
        undone = 0
        for mapping, weights in table.items():
            coefficients = [weights[k]] + [0] * m
            monomial = weights[k]
            for i, (column, doubled) in enumerate(zip(mapping, pattern)):
                value = x[i][column]
                monomial *= pow(value, 1 + doubled, prime)
                coefficients = convolution(coefficients, series(value, m, prime, doubled), m, prime)
            expected += monomial
            undone += coefficients[m]
        assert extracted == expected % prime
        columns.append(undone % prime)
    permanent = 0
    for mapping in maps:
        if len(set(mapping)) == m:
            value = 1
            for i, column in enumerate(mapping):
                value = value * x[i][column] % prime
            permanent += value
    assert sum(columns) % prime == permanent % prime
    return len(patterns)


def check_filters(m):
    tested = 0
    for row_counts in product(range(m + 1), repeat=m):
        bad = sum(count != 1 for count in row_counts)
        # J_i acts by (m-m), 1, or 0, according to the row support.
        eigenvalues = [sum((count == 0 or (count == 1 and j == 0)) for j in range(m))
                       - m * (count == 0) for count in row_counts]
        assert eigenvalues == [int(count == 1) for count in row_counts]
        assert sum(comb(bad, d) * (-1)**d for d in range(bad + 1)) == int(bad == 0)
        tested += 1
    return tested


def check_obstructions(m):
    blocks = m // 2
    forced = set()
    matching_forced = set()
    for mapping in product(range(m), repeat=m):
        pin = sum(1 << i for i in range(blocks) if mapping[2*i] == mapping[2*i+1])
        if len(set(mapping)) == m:
            assert pin == 0
            forced.add(0)
        elif pin:
            forced.add(pin)
        if all(set(mapping[2*i:2*i+2]) == {2*i, 2*i+1} for i in range(blocks)):
            swapped = sum(1 << i for i in range(blocks) if mapping[2*i] == 2*i+1)
            matching_forced.add(swapped)
    assert forced == matching_forced == set(range(1 << blocks))
    return len(forced)


def fiber_partitions(m):
    partitions = [()]
    for i in range(m):
        extended = []
        bit = 1 << i
        for blocks in partitions:
            extended.append((*blocks, bit))
            for j in range(len(blocks)):
                extended.append((*blocks[:j], blocks[j] | bit, *blocks[j+1:]))
        partitions = extended
    return partitions


def rank_mod(rows, prime):
    pivots = {}
    for original in rows:
        row = [x % prime for x in original]
        for i in sorted(pivots):
            if row[i]:
                multiple = row[i]
                row = [(a - multiple*b) % prime for a, b in zip(row, pivots[i])]
        first = next((i for i, x in enumerate(row) if x), None)
        if first is not None:
            inverse = pow(row[first], -1, prime)
            pivots[first] = [x * inverse % prime for x in row]
    return len(pivots)


def invariant_minimum(m, prime):
    equations = []
    for fibers in fiber_partitions(m):
        bijective = int(len(fibers) == m)
        row = [0] * (1 << m)
        row[0] = bijective - len(fibers)
        for block in fibers:
            row[block] += 1
        assert sum(row) == bijective
        equations.append(row)
    assert rank_mod(equations, prime) == (1 << m) - (m - 1)
    minimum = 1 << m
    for first in product(range(prime), repeat=m - 1):
        weights = [1]
        for b in (*first, -sum(first)):
            weights += [(w + b) % prime for w in weights]
        minimum = min(minimum, sum(w != 0 for w in weights))
    assert minimum * 8 >= 5 * (1 << m)
    if prime == 3:
        assert minimum * 8 == 5 * (1 << m)
    if prime > 2*m:
        assert minimum * 4 == 3 * (1 << m)
    return minimum


if __name__ == "__main__":
    rng = random.Random(261124)
    faces = sum(check_slices(m, p, rng) for m, p in [(2, 11), (3, 17), (4, 19)])
    filters = sum(check_filters(m) for m in range(1, 6))
    required = [check_obstructions(m) for m in (2, 4, 6)]
    print(f"{faces} Laurent slices and inverse-power checks; {filters} row-support profiles")
    print(f"Both perturbations force {required} columns for m=2,4,6")
    for m, prime in ((4, 3), (5, 3), (6, 3), (4, 5), (4, 11)):
        print(f"m={m}, field={prime}: minimum {invariant_minimum(m, prime)} fully symmetric slices")
