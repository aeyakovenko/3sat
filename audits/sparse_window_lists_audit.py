"""Check sparse Hamming balls against coordinate flats and exact sampling laws."""

from fractions import Fraction
from itertools import combinations
from math import comb


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def hit_count(length, cap, rank, weight, radius):
    return sum(
        choose(length - weight, added) * choose(weight, rank - added)
        for added in range(rank + 1)
        if added <= radius and weight + 2 * added <= cap + radius
    )


def audit_geometry():
    """Find nearest light completions directly by enumerating the Boolean cube."""
    checks = 0
    for length in range(1, 8):
        words = tuple(range(1 << length))
        for cap in range(length + 1):
            light = [word for word in words if word.bit_count() <= cap]
            supersets = {mask: [word for word in light if word & mask == mask]
                         for mask in light}
            # Centers of the same weight differ only by a coordinate permutation.
            for weight in range(length + 1):
                center = (1 << weight) - 1
                distances = {}
                for mask, candidates in supersets.items():
                    added = (mask & ~center).bit_count()
                    expected = added + max(0, weight + added - cap)
                    distances[mask] = min((word ^ center).bit_count()
                                          for word in candidates)
                    assert distances[mask] == expected
                for rank in range(cap + 1):
                    for radius in range(length + 1):
                        actual = sum(mask.bit_count() == rank and dist <= radius
                                     for mask, dist in distances.items())
                        assert actual == hit_count(length, cap, rank, weight, radius)
                        if radius < rank and weight <= cap + radius:
                            fraction = Fraction(actual, comb(length, rank))
                            upper = comb(rank, radius) * Fraction(weight, length) ** (rank - radius)
                            assert fraction <= upper
                        checks += 1
    return checks


def audit_mass():
    cases = 0
    for length in range(1, 10):
        for cap in range(length + 1):
            masses = [Fraction(1, (cap + 1) * comb(length, word.bit_count()))
                      for word in range(1 << length) if word.bit_count() <= cap]
            assert sum(masses) == 1
            for bits in range(length + 2):
                threshold = Fraction(1, 1 << bits)
                assert sum(prob >= threshold for prob in masses) <= 1 << bits
                cases += 1
    return cases


def audit_forced_masks():
    """Every light completion of a missed pattern evades a prescribed high-mass set."""
    checks = 0
    for length in range(2, 6):
        universe = range(1 << length)
        for cap in range(1, length):
            light = [word for word in universe if word.bit_count() <= cap]
            for rank in range(1, cap + 1):
                masks = [word for word in light if word.bit_count() == rank]
                for size in range(1, 4):
                    if size * comb(cap, rank) >= comb(length, rank):
                        continue
                    for high in combinations(universe, size):
                        mask = next(mask for mask in masks if not any(
                            word.bit_count() <= cap and word & mask == mask
                            for word in high))
                        assert all(word not in high for word in light
                                   if word & mask == mask)
                        checks += 1
    return checks


def audit_dyadic_charging():
    checks = 0
    for start in range(1, 4097):
        hit = [m for m in range(4, 16)
               if start <= 2**m and 2**m - m + 1 <= 2 * start]
        assert all(start <= 2**m <= 3 * start for m in hit)
        assert len(hit) <= 2
        checks += 1
    return checks


if __name__ == "__main__":
    print(f"{audit_geometry()} exact sparse-ball counts")
    print(f"{audit_mass()} normalized probability and superlevel counts")
    print(f"{audit_forced_masks()} forced low-mass masks")
    print(f"{audit_dyadic_charging()} dyadic reservation intervals")
