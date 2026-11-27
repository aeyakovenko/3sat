"""Exact checks for allocating one tag using only the completion epoch."""

from collections import Counter
from fractions import Fraction
from itertools import product


def tags(epoch):
    height = epoch.bit_length() - 1
    denominator = 1 << height.bit_length()
    law = Counter()
    for level in range(height + 1):
        width = 1 << level
        endpoint = (epoch // width + 1) * width - 1
        law[endpoint] += Fraction(1, denominator)
    return law


def prefix_blocks(cutoff):
    height = cutoff.bit_length() - 1
    blocks = [(1 << level, level) for level in range(height)]
    start = 1 << height
    remaining = cutoff - start + 1
    while remaining:
        level = remaining.bit_length() - 1
        blocks.append((start, level))
        start += 1 << level
        remaining -= 1 << level
    return blocks


def verify_coverage():
    visits = 0
    for cutoff in range(1, 257):
        blocks = prefix_blocks(cutoff)
        height = cutoff.bit_length() - 1
        assert len(blocks) <= 2 * height + 1
        cursor = 1
        for start, level in blocks:
            size = 1 << level
            assert start == cursor and start % size == 0
            cursor += size
            for epoch in range(start, cursor):
                assert tags(epoch)[cursor - 1] >= Fraction(1, 2 * (height + 1))
                visits += 1
        assert cursor == cutoff + 1
    return visits


def worst_case_examples():
    # The last dyadic endpoint remains inaccessible even with additive slack
    # H^2 in the epoch number, i.e. an enormous multiplicative clock allowance.
    checked = 0
    for height in range(12, 61):
        gap_level = (height * height + 1).bit_length()
        first_omitted = 1 << (height + 1)
        cutoff = first_omitted - (1 << gap_level) - 1
        rows = [first_omitted - (1 << (level + 1))
                for level in range(gap_level, height)]
        aggregate = Counter()
        for row in rows:
            for endpoint, probability in tags(row).items():
                if endpoint <= cutoff + height * height:
                    aggregate[endpoint] += probability / len(rows)
        expected = Fraction(1, len(rows) * (1 << height.bit_length()))
        assert max(aggregate.values()) == expected
        checked += 1
    return checked


def verify_grid_rounding():
    # A grid quantization transfers any fractional witness to a finite phase
    # search. Check against several kernels with overlapping stochastic columns.
    mistakes = 0
    for numerators in product(range(8), repeat=4):
        if sum(numerators) != 7:
            continue
        weights = [Fraction(m, 7) for m in numerators]
        denominator = 4 ** 3
        rounded = [int(p * denominator) for p in weights]
        for i in sorted(range(4), key=lambda i: weights[i] * denominator - rounded[i],
                        reverse=True)[:denominator - sum(rounded)]:
            rounded[i] += 1
        grid = [Fraction(m, denominator) for m in rounded]
        tv = sum(abs(p - v) for p, v in zip(weights, grid)) / 2
        assert tv <= Fraction(4, denominator)
        for column in ((1, 0, 1, 0), (0, Fraction(1, 3), Fraction(2, 3), 1)):
            drift = abs(sum((p - v) * z for p, v, z in zip(weights, grid, column)))
            assert drift <= tv
        mistakes += int(grid != weights)
    return mistakes


if __name__ == '__main__':
    visits = verify_coverage()
    cases = worst_case_examples()
    quantizations = verify_grid_rounding()
    print(f'{visits} covered epoch/cutoff pairs; {cases} sharp dyadic examples')
    print(f'{quantizations} nontrivial grid roundings with the certified error bound')
