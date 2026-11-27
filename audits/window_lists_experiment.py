"""Finite checks for the copying inequality and the feedback list budget."""

from fractions import Fraction
from itertools import combinations


def planted_profiles():
    width = 16
    first = 8
    kernel = {3: Fraction(1, 8), 5: Fraction(1, 16), 7: Fraction(1, 32)}
    kernel_weight = sum(kernel.values())
    max_plants = (1 - kernel_weight) * width // 4
    tested = 0
    for size in range(max_plants + 1):
        for offsets in combinations(range(width), size):
            planted = {first + i for i in offsets}
            masses = [Fraction(0)]
            for k in range(1, first + width + 24):
                seed = Fraction(2, width) if k in planted else Fraction(0)
                copied = sum(weight * masses[k - h]
                             for h, weight in kernel.items() if h < k)
                value = seed + copied
                assert (value * (1 << k)).denominator == 1
                masses.append(value)
            observed = {k for k in range(first, first + width)
                        if masses[k] > Fraction(1, width)}
            assert observed == planted
            assert sum(masses) <= Fraction(1, 2)
            tested += 1
    return tested


def feedback_budgets():
    # A common toy width 8 allows all tickets through the third stage.
    width = 8
    stages = 3
    tested = 0
    for size in range(width // 2 + 1):
        for positions in combinations(range(width * stages), size):
            bad = set(positions)
            success_count = 0
            hit_cost = 0
            miss_cost = 0
            for stage in range(stages):
                mask_size = width >> (success_count + 1)
                first = stage * width
                successful = any(i not in bad for i in range(first, first + mask_size))
                if successful:
                    hit_cost += mask_size
                    success_count += 1
                else:
                    miss_cost += mask_size
            assert hit_cost == width - (width >> success_count)
            assert miss_cost <= len(bad)
            tested += 1
    return tested


if __name__ == "__main__":
    print(f"{planted_profiles()} distinct planted patterns checked")
    print(f"{feedback_budgets()} finite feedback histories checked")
