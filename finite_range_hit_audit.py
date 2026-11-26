"""Exhaust finite tables of outputs and evaluator ranges for the one-hit premise."""

from itertools import combinations, product
from math import comb


def minimum_cover(indices, outputs, seed_values, hits, upper_bound):
    """Enumerate evaluator collections by size. Each bit in a mask names a table."""
    tables = list(product(range(outputs), repeat=indices))
    allowed = list(combinations(range(outputs), seed_values))
    masks = []
    expected_volume = sum(
        comb(indices, count) * seed_values**count * (outputs - seed_values) ** (indices - count)
        for count in range(hits, indices + 1)
    )
    for row in product(allowed, repeat=indices):
        mask = sum(
            1 << number
            for number, candidate in enumerate(tables)
            if sum(value in choices for value, choices in zip(candidate, row)) >= hits
        )
        assert mask.bit_count() == expected_volume
        masks.append(mask)
    target = (1 << len(tables)) - 1
    for size in range(1, upper_bound + 1):
        for collection in combinations(masks, size):
            covered = 0
            for mask in collection:
                covered |= mask
            if covered == target:
                return size
    raise AssertionError("no covering within the proposed bound")


def main():
    cases = [
        (2, 4, 2, [2, 4]),
        (3, 2, 1, [2, 2, 8]),
        (4, 2, 1, [2, 2, 4, 16]),
        (2, 4, 1, [4, 16]),
    ]
    for indices, outputs, seed_values, expected in cases:
        results = [
            minimum_cover(indices, outputs, seed_values, hits, bound)
            for hits, bound in enumerate(expected, 1)
        ]
        assert results == expected
        assert results[0] == outputs // seed_values
        assert results[-1] == (outputs // seed_values) ** indices
        print(f"L={indices} q={outputs} B={seed_values}, minima by hit count: {results}")


if __name__ == "__main__":
    main()
