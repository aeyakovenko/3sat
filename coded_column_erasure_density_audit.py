"""Exact density and erased-fiber checks for small binary column codes.

For each summary, arbitrary short labels are allowed: choose the 2^s label
fibers with the most high-density inputs. No sampling of X, K or J is used.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import comb
from random import Random


def masks(d, k):
    return [sum(1 << j for j in c) for c in combinations(range(d), k)]


def columns(mask, width, rows):
    return sum(mask << (i * width) for i in range(rows))


def span(words):
    generated = {0}
    for word in words:
        generated.update([word ^ x for x in generated])
    return generated


def matrix_values(a, d, b):
    m = len(b)
    row_products = [sum(((x & col).bit_count() % 2) << j for j, col in enumerate(b))
                    for x in range(1 << d)]
    return [sum(row_products[(x >> (i * d)) % (1 << d)] << (i * m) for i in range(a))
            for x in range(1 << (a * d))]


def summary_labels(a, d, b, values, kind):
    rng = Random(167 * a + 41 * d + sum(b))
    if kind == "none":
        return [0] * len(values)
    if kind == "product":
        return values
    if kind == "rare":
        return [int(y == 0) for y in values]
    if kind == "nonlinear":
        return [((x & 1) * ((y >> 1) & 1)) | (((x ^ y).bit_count() % 2) << 1)
                for x, y in enumerate(values)]
    if kind == "random":
        return [rng.randrange(7) for _ in values]
    if kind == "parity_remainder":
        assert b == ((1 << d) - 1,)
        return [y ^ sum(((x >> (d * i)) & 1) << i for i in range(a))
                for x, y in enumerate(values)]
    raise ValueError(kind)


def fibers_and_cheaps(a, d, m, values, labels):
    n = len(values)
    output_bits = (1 << (a * m)) - 1
    # For each number t of affordable columns, cheap[t][x] counts the
    # individual coordinates with SOME certificate of size <=t on input x.
    affordable = [0] * n
    cheap, forced_on, strata = [], {}, {}
    for size in range(d + 1):
        for observed in masks(d, size):
            visible = columns(observed, d, a)
            keys = [(x & visible, z) for x, z in enumerate(labels)]
            cells = {}
            for key, y in zip(keys, values):
                if key in cells:
                    mass, always, ever = cells[key]
                    cells[key] = (mass + 1, always & y, ever | y)
                else:
                    cells[key] = (1, y, y)
            cells = {key: (mass, output_bits ^ (always ^ ever))
                     for key, (mass, always, ever) in cells.items()}
            fixed = [cells[key][1] for key in keys]
            strata[observed] = list(cells.values())
            forced_on[observed] = fixed
            for x, bits in enumerate(fixed):
                affordable[x] |= bits
        cheap.append([bits.bit_count() for bits in affordable])
    assert all(q == a * m for q in cheap[-1])
    return cheap, forced_on, strata


def top_mass(weights, s):
    return sum(sorted(weights.values(), reverse=True)[:1 << s])


def audit(a, d, b, kind, counts):
    n, m = 1 << (a * d), len(b)
    all_inputs = (1 << d) - 1
    code = span(b)
    distance = min(x.bit_count() for x in code if x)
    values = matrix_values(a, d, b)
    labels = summary_labels(a, d, b, values, kind)
    cheap, forced_on, strata = fibers_and_cheaps(a, d, m, values, labels)
    if kind == "none":
        for t in range(d + 1):
            assert set(cheap[t]) == {a * sum(col.bit_count() <= t for col in b)}
    if kind == "product":
        assert all(q == a * m for q in cheap[0])
    if kind == "rare" and (a, d, b) == (4, 3, (0b111,)):
        # With all columns erased, Z=1 means Y=0. Four bits are then forced
        # with conditional probability one, but the joint mass is exactly 2^-4.
        positive_label = [x for x, z in enumerate(labels) if z]
        assert F(len(positive_label), n) == F(1, 16)
        assert all(forced_on[0][x] == 15 for x in positive_label)
        counts["conditional_regression"] += 1
    if kind == "parity_remainder":
        assert set(cheap[0]) == {0} and set(cheap[1]) == {a * m}

    caps = range((len(set(labels)) - 1).bit_length() + 1)
    # Density thresholds q/(a*m), including every achievable fraction.
    best = {}
    for t, density in enumerate(cheap):
        by_size = [Counter() for _ in range(a * m + 1)]
        for z, q in zip(labels, density):
            by_size[q][z] += 1
        qualifying = Counter()
        for q in reversed(range(a * m + 1)):
            qualifying.update(by_size[q])
            for s in caps:
                best[t, q, s] = top_mass(qualifying, s)

    for k in range(1, d + 1):
        erased_sets = masks(d, k)
        for ell in range(1, min(k, m) + 1):
            output_sets = masks(m, ell)
            trials = len(erased_sets) * len(output_sets)
            slots = a * ell
            # Hit histograms are later accumulated into upper tails.
            hist = [[0] * n for _ in range(slots + 1)]
            bad = dependent = 0
            for tested in output_sets:
                selected = [b[j] for j in range(m) if tested >> j & 1]
                image = span(selected)
                if len(image) < (1 << ell):
                    dependent += 1
                out_bits = columns(tested, m, a)
                for erased in erased_sets:
                    if len({v & erased for v in image}) != 1 << ell:
                        bad += 1
                        continue
                    observed = all_inputs ^ erased
                    for mass, fixed in strata[observed]:
                        h_fixed = (fixed & out_bits).bit_count()
                        # Joint conditional on outside columns and (K,J): count
                        # X_inside with the specified state AND its fixed bits.
                        assert mass <= 1 << (a * k - h_fixed)
                        counts["fiber"] += 1
                    for x, f in enumerate(forced_on[observed]):
                        hist[(f & out_bits).bit_count()][x] += 1

            # Distance controls erasure failure only for independent tested columns.
            delta_failure = F(comb(d - distance, k), comb(d, k)) * ((1 << ell) - 1)
            p_dependent = F(dependent, len(output_sets))
            assert F(bad, trials) <= p_dependent + (1 - p_dependent) * delta_failure
            hits = [0] * n
            for h in reversed(range(1, slots + 1)):
                for x, exact in enumerate(hist[h]):
                    hits[x] += exact
                good_by_label = Counter()
                for z, count in zip(labels, hits):
                    good_by_label[z] += count
                for s in caps:
                    assert F(top_mass(good_by_label, s), n * trials) <= F(1 << s, 1 << h)
                for t, density in enumerate(cheap):
                    minimum = {}
                    for q, num in zip(density, hits):
                        if num < minimum.get(q, trials + 1):
                            minimum[q] = num
                    avoid = F(comb(d - t, k), comb(d, k))
                    for q, least in minimum.items():
                        predicted = F(q, a * m) * avoid
                        # Also check the tail bound using that a miss forces at most h-1 bits.
                        sharp = (slots * predicted - h + 1) / (slots - h + 1) - F(bad, trials)
                        lower = predicted - F(bad, trials) - F(h, slots)
                        assert F(least, trials) >= max(0, sharp, lower)
                        counts["per_density"] += 1
                    for q in range(a * m + 1):
                        lower = F(q, a * m) * avoid - F(bad, trials) - F(h, slots)
                        for s in caps:
                            actual = F(best[t, q, s], n)
                            rhs = F(1 << s, 1 << h)
                            assert actual * lower <= rhs
                            counts["global"] += 1
                            if 0 < actual and rhs < lower:
                                counts["informative"] += 1
                                if 0 < t and k < d:
                                    counts["interior"] += 1
                            if (kind == "parity_remainder" and
                                    (a, d, k, ell, t, h, q, s) == (5, 3, 1, 1, 1, 2, 5, 0)):
                                assert (actual, lower, rhs) == (F(1, 32), F(4, 15), F(1, 4))
                                counts["example"] += 1
    counts["instances"] += 1
    counts["inputs"] += n


def main():
    counts = Counter()
    for a, d, b in [(3, 3, (0b011, 0b101)), (3, 4, (0b1101, 0b1011)),
                    (4, 3, (0b111,)), (2, 3, (0b111, 0b111))]:
        for kind in ("none", "product", "rare", "nonlinear", "random"):
            audit(a, d, b, kind, counts)
    audit(5, 3, (0b111,), "parity_remainder", counts)
    assert counts["conditional_regression"] == counts["example"] == 1 and counts["interior"] > 0
    print(f"{counts['instances']} code/summary cases and {counts['inputs']} exhaustive inputs; "
          f"{counts['fiber']} good-rank fiber bounds and {counts['per_density']} conditional density bounds.")
    print(f"{counts['global']} extremal short-state inequalities; {counts['informative']} yielded "
          f"a bound below one with positive observed mass, {counts['interior']} with t>0 and k<d.")
    print("Five-row parity example: all certificates have size one; P(short and dense)=1/32, "
          "conditional-event lower bound=4/15, 2^(s-h)=1/4.")


if __name__ == "__main__":
    main()
