"""Exhaust the signed reduction on small batches with data-dependent gray answers."""

from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations, product
from math import prod


def good(record):
    return int(record % 2 == 0)


def make_tester(width, tolerance):
    def test(records):
        assert len(records) == width
        defects = sum(1 - good(record) for record in records)
        if not defects:
            return 1
        if defects > tolerance * width:
            return 0
        return (sum((i + 1) * record for i, record in enumerate(records)) % 5) - 2

    return test


def compacted_terms(records, capacity):
    """Each selected subset gets one encoding, with independent signed switches."""
    terms = Counter()
    for size in range(capacity + 1):
        for chosen in combinations(range(len(records)), size):
            for switches in product((0, 1), repeat=size):
                payload = tuple(records[i] if on else 0 for i, on in zip(chosen, switches))
                payload += (0,) * (capacity - size)
                terms[payload] += (-1) ** (size + sum(switches))
    return {payload: weight for payload, weight in terms.items() if weight}


def make_reconstructor(width, tolerance):
    test = make_tester(width, tolerance)
    shrink = (1 + tolerance) / 2

    @cache
    def reconstruct(records):
        if not records:
            return 1
        groups = [records[i:i + width] for i in range(0, len(records), width)]
        verdicts = []
        next_terms = []
        for group in groups:
            repeated = tuple(group[i % len(group)] for i in range(width))
            verdicts.append(test(repeated))
            capacity = int(shrink * len(group))
            next_terms.append(compacted_terms(group, capacity).items())

        correction = 0
        for choices in product(*next_terms):
            next_records = sum((row for row, _ in choices), ())
            assert len(next_records) < len(records)
            correction += prod(weight for _, weight in choices) * reconstruct(next_records)
        return prod(verdicts) * correction

    return reconstruct


def main():
    cases = 0
    for width, tolerance in product(range(1, 5), (Fraction(0), Fraction(1, 2), Fraction(3, 4))):
        reconstruct = make_reconstructor(width, tolerance)
        for size in range(6):
            for records in product(range(4), repeat=size):
                assert reconstruct(records) == prod(map(good, records))
                cases += 1
    test = make_tester(3, Fraction(1, 2))
    assert test((1, 0, 0)) != test((3, 0, 0))
    print(f"Verified {cases:,} raw batches, including gray outputs varying at fixed verdicts.")


if __name__ == "__main__":
    main()
