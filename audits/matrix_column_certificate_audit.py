"""Exact finite checks for whole-column certificates of binary matrix products.

Every X, column mask and output mask is enumerated. Entropy inequalities use
integer powers, including when the summary has unequal, non-power-of-two fibers.
"""
from collections import Counter
from itertools import combinations
from math import comb, prod
from random import Random


def selected(mask, d):
    return [i for i in range(d) if mask >> i & 1]


def subsets(d, k):
    return [sum(1 << i for i in positions) for positions in combinations(range(d), k)]


def word_columns(mask, d):
    """Row-major word containing the same selected column bits in every row."""
    return sum(mask << (i * d) for i in range(d))


def subrank(rows_b, inner, out, d):
    pivots = {}
    for h in selected(inner, d):
        row = rows_b[h] & out
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def products(rows_b, d):
    row_outputs = [0] * (1 << d)
    for mask in range(1, 1 << d):
        high = mask.bit_length() - 1
        row_outputs[mask] = row_outputs[mask ^ (1 << high)] ^ rows_b[high]
    return [sum(row_outputs[(x >> (i * d)) % (1 << d)] << (i * d) for i in range(d))
            for x in range(1 << (d * d))]


def summaries(values, d, rng):
    return {
        "constant": [0] * len(values),
        "product": values,
        "first_column": [v & word_columns(1, d) for v in values],
        "nonlinear": [(v & 1) | ((((x >> 1) & (v >> d)) & 1) << 1)
                      for x, v in enumerate(values)],
        "rare_flag": [int(x == 0) for x in range(len(values))],
        "random_map": [rng.randrange(5) for _ in values],
    }


def matrix_inputs(d, rng):
    """All invertible matrices in d<=2; 24 distinct invertible ones in d=3."""
    full = (1 << d) - 1
    invertible = []
    singular = []
    for mask in range(1 << (d * d)):
        rows = tuple((mask >> (i * d)) & full for i in range(d))
        if subrank(rows, full, full, d) == d:
            invertible.append(rows)
        else:
            singular.append(rows)
    if d == 3:
        identity = tuple(1 << i for i in range(d))
        invertible.remove(identity)
        invertible = [identity, *rng.sample(invertible, 23)]
    # Zero and one nonzero singular matrix are useful degeneracies.
    extras = [singular[0]]
    if len(singular) > 1:
        extras.append(singular[-1])
    return [(b, True) for b in invertible] + [(b, False) for b in extras]


def audit(rows_b, values, z, kind, d, counts):
    full = (1 << d) - 1
    n = len(values)
    coordinates = d * d
    all_coordinates = (1 << coordinates) - 1
    # For each x and i,j, the smallest number of observed columns that fixes y_ij.
    costs = [[d + 1] * coordinates for _ in values]
    # Each list contains (fiber cardinality, forced output-bit mask).
    fibers = {}
    for size in range(d + 1):
        for observed in subsets(d, size):
            visible_bits = word_columns(observed, d)
            keys = [(key, x & visible_bits) for x, key in enumerate(z)]
            groups = {}
            for key, output in zip(keys, values):
                if key in groups:
                    mass, always_one, ever_one = groups[key]
                    groups[key] = (mass + 1, always_one & output, ever_one | output)
                else:
                    groups[key] = (1, output, output)
            forced = {key: (mass, all_coordinates ^ (always_one ^ ever_one))
                      for key, (mass, always_one, ever_one) in groups.items()}
            fibers[observed] = tuple(forced.values())
            for x, key in enumerate(keys):
                fixed = forced[key][1]
                for entry in range(coordinates):
                    if fixed >> entry & 1 and costs[x][entry] > size:
                        costs[x][entry] = size

    distribution = Counter(c for row in costs for c in row)
    assert max(distribution) <= d
    if kind == "constant":
        weights = [sum((row >> j) & 1 for row in rows_b) for j in range(d)]
        assert all(row == weights * d for row in costs)
    if kind == "product":
        assert distribution == {0: n * coordinates}
    counts["certificates"] += n * coordinates

    masses = Counter(z).values()
    entropy_denominator = prod(mass ** mass for mass in masses)
    for k in range(d + 1):
        choices = subsets(d, k)
        ways = len(choices)
        forced_total = rank_loss_sum = 0
        for erased in choices:
            strata = fibers[full ^ erased]
            for output in choices:
                output_mask = word_columns(output, d)
                loss = d * (k - subrank(rows_b, erased, output, d))
                rank_loss_sum += loss
                for mass, fixed in strata:
                    h = (fixed & output_mask).bit_count()
                    # Fixing outside columns and z leaves a single fiber. Each
                    # projected value has at most 2^loss erased-block preimages.
                    assert mass <= 1 << (loss + d * k - h)
                    forced_total += mass * h
                    counts["fibers"] += 1

        weighted = sum(number * comb(d - c, k) for c, number in distribution.items())
        # forced_total/(n*ways^2) >= d*k*E[binom(d-c,k)]/ways.
        assert d * forced_total >= k * ways * weighted
        if kind in ("constant", "product"):
            assert d * forced_total == k * ways * weighted
        # n*ways^2 H(Z) = n*ways^2 log2(n) - ways^2 sum_z mass log2(mass).
        # Exponentiate the upper bound exactly to avoid rounding logarithms.
        information_needed = forced_total - n * rank_loss_sum
        exponent = n * ways * ways * coordinates - information_needed
        assert exponent >= 0 and (1 << exponent) >= entropy_denominator ** (ways * ways)
        if k:
            counts["positive_k"] += 1
        else:
            assert forced_total == rank_loss_sum == 0
            counts["zero_k"] += 1
        if d * forced_total > k * ways * weighted:
            counts["strict_lower"] += 1


def main():
    rng = Random(514227)
    counts = Counter()
    for d in (1, 2, 3):
        for matrix, invertible in matrix_inputs(d, rng):
            counts["invertible" if invertible else "singular"] += 1
            values = products(matrix, d)
            # Independent bit-level dot products, including every output position.
            for x, result in enumerate(values):
                for i in range(d):
                    for j in range(d):
                        dot = sum(((x >> (i * d + h)) & 1) * ((matrix[h] >> j) & 1)
                                  for h in range(d)) % 2
                        assert (result >> (i * d + j)) & 1 == dot
            for kind, z in summaries(values, d, rng).items():
                audit(matrix, values, z, kind, d, counts)
    assert counts["strict_lower"] > 0
    print(f"{counts['invertible']} invertible and {counts['singular']} singular multipliers; "
          f"6 summaries each. {counts['certificates']} minimum whole-column certificates.")
    print(f"{counts['positive_k']} positive-k and {counts['zero_k']} zero-k average inequalities "
          f"passed exactly, with {counts['strict_lower']} strict lower bounds. "
          f"{counts['fibers']} pointwise fiber-size bounds passed.")


if __name__ == "__main__":
    main()
