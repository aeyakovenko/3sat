"""Optimal depth-limited bit-query trees on uniform random truth tables.

Run with --sample for seeded numerical estimates (requires NumPy). The default
uses only the standard library, exhausts four-bit truth tables and counts
five-bit truth tables by symmetry for a one-query tree.
"""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, log, sqrt


def one_query_agreements(table, dimension):
    """Best number of agreements with a constant or a single-coordinate test."""
    inputs = 1 << dimension
    positives = table.bit_count()
    best = max(positives, inputs - positives)
    for coordinate in range(dimension):
        on = sum(1 << x for x in range(inputs) if x & (1 << coordinate))
        high = (table & on).bit_count()
        low = positives - high
        best = max(best, max(high, inputs // 2 - high) + max(low, inputs // 2 - low))
    return best


def audit_one_query(dimension):
    inputs = 1 << dimension
    counts = [0] * (inputs + 1)
    for table in range(1 << inputs):
        counts[one_query_agreements(table, dimension)] += 1
    mean = Fraction(sum(i * n for i, n in enumerate(counts)), inputs * (1 << inputs))
    return mean, counts


def exact_five_bit_mean():
    """Exhaust the 2^32 pairs of four-bit halves via first-Walsh-coefficient symmetry."""
    masks = [sum(1 << x for x in range(16) if x & (1 << i)) for i in range(4)]
    first = Counter()
    second = Counter()
    for table in range(1 << 16):
        ones = table.bit_count()
        total = abs(2 * ones - 16)
        w = tuple(2 * (2 * (table & mask).bit_count() - ones) for mask in masks)
        # Translations and coordinate permutations act on the w's by
        # independent sign flips and permutations, without changing total.
        first[(total, *sorted(map(abs, w)))] += 1
        second[(total, *w)] += 1
    count = 0
    for a, n in first.items():
        for b, m in second.items():
            # On the full five-bit table a query can use either half's
            # membership or one of their four common axes.
            advantage = max(a[0] + b[0], *(abs(a[i] + b[i]) for i in range(1, 5)))
            count += n * m * ((32 + advantage) // 2)
    return Fraction(count, 32 * (1 << 32))


def entropy_upper_test(omitted, z, target):
    """Exact test of a_k < target from majority labels on a fixed tree shape."""
    leaf_size = 1 << omitted
    moment = sum(comb(leaf_size, j) * z**max(j, leaf_size-j) for j in range(leaf_size+1))
    moment /= 2**leaf_size
    # For depth r-k, the log of the number of query shapes per leaf is
    # at most sum_{i>=1} 2^(-i) log(k+i) <= log(k+2).
    # Given a shape, leaf majorities have iid scores with the above moment.
    # Jensen and the union bound for the exponential moment give
    # a_k <= log((k+2)*moment) / (leaf_size*log(z)).
    return ((omitted+2) * moment)**target.denominator < z**(leaf_size * target.numerator)


def random_optimal_scores(tables, omitted, np):
    """One exact optimal score per supplied table; vectorize over samples and faces."""
    samples, inputs = tables.shape
    dimension = inputs.bit_length() - 1
    assert 1 << dimension == inputs and 0 <= omitted <= dimension
    previous = {0: tables.astype(np.int32)}
    if omitted == 0:
        return np.full(samples, inputs)
    for width in range(1, dimension + 1):
        current = {}
        for coords in combinations(range(dimension), width):
            free = sum(1 << c for c in coords)
            best = None
            # Before the depth cap is reached, collect counts of ones over
            # a face. One split suffices because that count is additive.
            choices = coords if width > omitted else coords[:1]
            for c in choices:
                child = free ^ (1 << c)
                # Child face assignments are packed in increasing coordinate
                # order, omitting all the child's free coordinates.
                low = 1 << (c - (child & ((1 << c) - 1)).bit_count())
                pair = previous[child].reshape(samples, -1, 2, low)
                score = (pair[:, :, 0, :] + pair[:, :, 1, :]).reshape(samples, -1)
                if best is None:
                    best = score
                else:
                    np.maximum(best, score, out=best)
            if width == omitted:
                # Optimal terminal answer is the majority bit on this face.
                best = np.maximum(best, (1 << width) - best)
            current[free] = best
        previous = current
    return previous[(1 << dimension) - 1][:, 0]


def increment_tail_bound(r):
    """Upper bound on sum_{n>r} sqrt(ln(n)/(2*2^n)).

    Use log(r+j) <= log(r+1)+(j-1)/(r+1) and the tangent-line upper bound
    on its square root; then sum both geometric series in closed form.
    """
    q = 1 / sqrt(2)
    base = sqrt(log(r + 1))
    return q**(r + 1) / sqrt(2) * (
        base / (1 - q) + q / (2 * (r+1) * base * (1-q)**2)
    )


def no_query_mean(omitted):
    inputs = 1 << omitted
    return Fraction(1, 2) + Fraction(comb(inputs, inputs//2), 2 * 2**inputs)


def run_sample(dimensions, omissions, samples, batch_size, seed):
    import numpy as np
    from inverse_trace_subcube_audit import positive_roots

    rng = np.random.default_rng(seed)
    # Independent implementation of the four-bit exhaustive check above.
    for start in range(0, 1 << 16, 1024):
        values = np.arange(start, start + 1024, dtype=np.uint32)
        tables = ((values[:, None] >> np.arange(16, dtype=np.uint32)) & 1)
        expected = [one_query_agreements(x, 4) for x in range(start, start + 1024)]
        assert np.array_equal(random_optimal_scores(tables, 3, np), expected)
    for r in (6, 8):
        polynomial, mask = positive_roots(r)
        table = np.array([[(mask >> x) & 1 for x in range(1 << r)]], dtype=np.uint8)
        for k in (3, 4, 5):
            score = int(random_optimal_scores(table, k, np)[0])
            print(f"Exact inverse trace, polynomial {polynomial:#x}, r={r}, k={k}: {score}/{1 << r}")
    print(f"Seed {seed}, {samples} uniform tables per dimension; estimates are numerical.")
    for r in dimensions:
        totals = {k: 0 for k in omissions if k <= r}
        for start in range(0, samples, batch_size):
            count = min(batch_size, samples - start)
            tables = rng.integers(2, size=(count, 1 << r), dtype=np.uint8)
            for k in totals:
                totals[k] += int(random_optimal_scores(tables, k, np).sum())
        means = ", ".join(f"k={k}: {total / (samples * (1 << r)):.6f}"
                          for k, total in totals.items())
        print(f"r={r}: {means}; analytic tail ≤ {increment_tail_bound(r):.6f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sample", action="store_true")
    parser.add_argument("--dimensions", nargs="+", type=int, default=[7, 9, 11])
    parser.add_argument("--omissions", nargs="+", type=int, default=[4, 5])
    parser.add_argument("--samples", type=int, default=256)
    parser.add_argument("--batch", type=int, default=8)
    parser.add_argument("--seed", type=int, default=27127)
    args = parser.parse_args()
    for r in (2, 3, 4):
        mean, histogram = audit_one_query(r)
        print(f"Exact one-query mean for r={r}, k={r-1}: {mean} = {float(mean):.8f}")
    assert mean == Fraction(45407, 65536)
    print("Exact counts of four-bit truth tables by number of correct answers:")
    print({score: n for score, n in enumerate(histogram) if n})
    print(f"Exact constant-only mean for k=3: {no_query_mean(3)}")
    five_bit_mean = exact_five_bit_mean()
    assert five_bit_mean == Fraction(21642017, 33554432)
    print(f"Exact one-query mean for r=5, k=4: {five_bit_mean}")
    for k, z, target in ((4, Fraction(13, 4), Fraction(771, 1000)),
                         (5, Fraction(23, 10), Fraction(7, 10)),
                         (6, Fraction(9, 5), Fraction(323, 500))):
        assert entropy_upper_test(k, z, target)
        print(f"Exact rational exponential-moment upper certificate: a_{k} < {target}")
    if args.sample:
        run_sample(args.dimensions, args.omissions, args.samples, args.batch, args.seed)
