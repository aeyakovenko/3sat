"""Check signed witness subsets, prime-power divisibility, and disjoint list faces."""

from itertools import combinations, product
from math import comb


def check_binomial_filter():
    trials = 0
    for prime in (2, 3, 5, 7):
        for exponent in (1, 2, 3):
            divisor = prime**exponent
            slots = divisor - 1
            for count in range(2 * divisor + 10):
                value = sum((-1) ** (j + 1) * comb(count, j)
                            for j in range(1, min(slots, count) + 1))
                assert value % prime == int(count % divisor != 0)
                trials += 1
    return trials


def check_slots():
    trials = 0
    universe = range(5)
    for support_mask in range(1 << len(universe)):
        support = {i for i in universe if support_mask & (1 << i)}
        for prime, exponent in ((2, 1), (2, 2), (3, 1), (5, 1)):
            divisor = prime**exponent
            slots = divisor - 1
            observed = 0
            for active in range(1, slots + 1):
                for row in combinations(universe, active):
                    if all(y in support for y in row):
                        observed += (-1) ** (active + 1)
            assert observed % prime == int(len(support) % divisor != 0)
            trials += 1
    return trials


def check_faces():
    trials = 0
    for first in range(8):
        for second in range(8):
            if first == second:
                continue
            for a, b in product(range(4), repeat=2):
                rows = (first, second, 12 + a, 12 + b)
                assert (len(set(rows)) == len(rows)) == (a != b)
                trials += 1
    return trials


if __name__ == "__main__":
    print(f"{check_binomial_filter()} prime-power thresholds, "
          f"{check_slots()} signed witness tables, {check_faces()} restricted list inputs")
