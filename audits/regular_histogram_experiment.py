"""Exact checks for clipped quadratic energy on dyadic subprobability measures."""

from fractions import Fraction
from math import comb

ZERO = Fraction(0)
ONE = Fraction(1)


def clipped(x, threshold):
    if x <= threshold:
        return x * x
    return threshold * (2 * x - threshold)


def average(values):
    return sum(values, ZERO) / len(values)


def densities(weights, denominator):
    size = len(weights)
    assert size > 0 and size & (size - 1) == 0
    assert min(weights) >= 0 and sum(weights) <= denominator
    levels = [[Fraction(size * w, denominator) for w in weights]]
    while len(levels[-1]) > 1:
        fine = levels[-1]
        levels.append([(p + q) / 2 for p, q in zip(fine[::2], fine[1::2])])
    return levels[::-1]


def check(levels, threshold):
    assert threshold > 0 and len(levels) >= 2
    mass = levels[0][0]
    energies = [average([clipped(x, threshold) for x in row]) for row in levels]
    increments = []
    sparse_sizes = []
    for depth, children in enumerate(levels[1:]):
        parents = levels[depth]
        count = len(children)
        assert average(children) == mass
        divergences = []
        light_differences = []
        high_children = set()
        below_high_parents = set()
        for j, x in enumerate(children):
            y = parents[j // 2]
            divergence = clipped(x, threshold) - clipped(y, threshold)
            divergence -= 2 * min(y, threshold) * (x - y)
            assert divergence >= 0
            divergences.append(divergence)
            if x > threshold:
                high_children.add(j)
            if y > threshold:
                below_high_parents.add(j)
            if x <= threshold and y <= threshold:
                difference = abs(x - y)
                assert difference**2 == divergence
                light_differences.append(difference)

        delta = energies[depth + 1] - energies[depth]
        increments.append(delta)
        assert delta == average(divergences)
        light_l1 = sum(light_differences, ZERO) / count
        light_l2_sq = sum((d * d for d in light_differences), ZERO) / count
        light_fraction = Fraction(len(light_differences), count)
        assert light_l1**2 <= light_fraction * light_l2_sq <= delta
        sparse = high_children | below_high_parents
        assert len(sparse) + len(light_differences) == count
        assert len(high_children) * threshold <= count * mass
        assert len(below_high_parents) * threshold <= count * mass
        assert len(sparse) * threshold <= 2 * count * mass <= 2 * count
        sparse_sizes.append(len(sparse))

    assert sum(increments, ZERO) == energies[-1] - energies[0]
    assert energies[-1] <= 2 * threshold * mass
    for first in range(len(increments)):
        for end in range(first + 1, len(increments) + 1):
            window = increments[first:end]
            assert len(window) * min(window) <= energies[end] - energies[first]
            assert energies[end] - energies[first] <= 2 * threshold * mass
    return increments, sparse_sizes


def histograms(size, budget):
    """All integer subprobability numerators of total at most budget."""
    if size == 0:
        yield ()
        return
    for first in range(budget + 1):
        for tail in histograms(size - 1, budget - first):
            yield (first,) + tail


def exhaustive():
    thresholds = (ONE / 2, ONE, Fraction(3, 2), Fraction(2), Fraction(3))
    for size, budget in ((2, 6), (4, 5), (8, 4), (16, 2)):
        count = 0
        for weights in histograms(size, budget):
            levels = densities(weights, budget)
            for threshold in thresholds:
                check(levels, threshold)
            count += 1
        assert count == comb(size + budget, size)
        print(f"{size} bins, denominator {budget}: {count} histograms, "
              f"{len(thresholds)} thresholds")


def multiscale():
    threshold = Fraction(3, 2)
    for depth in (4, 6, 8, 10):
        size = 1 << depth
        weights = [1 + i.bit_count() + (i % 7 == 0) * depth
                   + (i < size // 8) * (3 * depth) for i in range(size)]
        weights[size // 2] += size
        levels = densities(weights, sum(weights) + size // 8)
        increments, sparse = check(levels, threshold)
        best = min(range(depth), key=increments.__getitem__)
        assert any(sparse) and any(d > 0 for d in increments)
        print(f"pattern {size}: least increment {increments[best]} "
              f"at {1 << best}->{2 << best} bins; "
              f"exceptional positions {sparse[best]}/{2 << best}")


if __name__ == "__main__":
    exhaustive()
    multiscale()
