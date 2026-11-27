"""Exact checks for the weighted hitting potential. Run with Python 3.10+.

A D-bit seed chooses one row S. Enumerating multisets of 2**D rows
covers every empirical joint law of the item indicators up to seed order.
"""

from fractions import Fraction
from itertools import combinations_with_replacement
from math import ceil, comb


def weight(n, k, size, hits):
    return Fraction(1, 2**hits) / Fraction(2 * n - size, 2 * n) ** k


def qualification(phi, count, depth, k):
    # These are exactly the integers e with 2**(e-2) <= count <= 8*2**e.
    first = (count - 1).bit_length() - 3
    last = count.bit_length() + 1
    assert first <= last
    for exponent in range(first, last + 1):
        estimate = Fraction(2) ** exponent
        assert estimate / 4 <= count <= 8 * estimate
        qualifies = exponent <= depth + k + 3
        assert phi > 1 or qualifies
        assert not qualifies or phi <= 64


def test_seed_tables(n, depth):
    masks = range(2**n)
    size = {s: s.bit_count() for s in masks}
    by_k = [[h for h in masks if size[h] == k] for k in range(n + 1)]
    samples = 2**depth
    cells = {}
    bounds = {}
    for k, choices in enumerate(by_k):
        for h in choices:
            for s in masks:
                hits = (s & h).bit_count()
                w = weight(n, k, size[s], hits)
                cells[h, s] = hits, w, ceil(2**k * w)
        # For a threshold delta with ceil(delta*N)=d, d/N is strongest.
        for d in range(n + 1):
            for b in range(k + 1):
                bounds[k, d, b] = samples * 2**b * Fraction(2 * n - d, 2 * n) ** k

    laws = variable_sizes = choices_tested = low_potential = 0
    for rows in combinations_with_replacement(masks, samples):
        laws += 1
        variable_sizes += len({size[s] for s in rows}) > 1
        for k, choices in enumerate(by_k):
            potentials = []
            for h in choices:
                entries = [cells[h, s] for s in rows]
                phi = sum(w for _, w, _ in entries) / samples
                qualification(phi, sum(z for _, _, z in entries), depth, k)
                potentials.append(phi)
                choices_tested += 1
                if phi <= 1:
                    low_potential += 1
                    for d in range(n + 1):
                        for b in range(k + 1):
                            bad = sum(size[s] >= d and hits <= b
                                      for s, (hits, _, _) in zip(rows, entries))
                            assert bad <= bounds[k, d, b], (rows, h, d, b)
            assert sum(potentials) <= len(choices), (rows, k, potentials)
            assert min(potentials) <= 1
    return laws, variable_sizes, choices_tested, low_potential


def test_single_rows():
    # Count every K-subset by its intersection size. This includes rare
    # deviations past 64 without materializing exponentially many centers.
    cases = extreme = 0
    for n in (*range(1, 10), 40):
        for k in range(n + 1):
            for size in range(n + 1):
                total = Fraction(0)
                centers = 0
                for hits in range(max(0, k + size - n), min(k, size) + 1):
                    count = comb(size, hits) * comb(n - size, k - hits)
                    w = weight(n, k, size, hits)
                    qualification(w, ceil(2**k * w), 0, k)
                    total += count * w
                    centers += count
                    extreme += w > 64
                assert centers == comb(n, k)
                assert total <= centers
                cases += 1
    assert extreme
    return cases, extreme


if __name__ == "__main__":
    counts = [0, 0, 0, 0]
    for n in range(1, 5):
        for depth in (1, 2):
            for i, count in enumerate(test_seed_tables(n, depth)):
                counts[i] += count
    cases, extreme = test_single_rows()
    print(f"{counts[0]} seed-table laws ({counts[1]} with variable row sizes) and "
          f"{counts[2]} centers passed. All {counts[3]} centers with potential at most "
          "one passed every tail threshold.")
    print(f"{cases} single-row size cases passed; "
          f"{extreme} intersection classes had potential greater than 64.")
