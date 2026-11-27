"""Finite checks of the monotone-summary characterization. Python 3, no dependencies."""

from collections import Counter
from itertools import product


def included(a, b):
    return a & b == a


def strict_pairs(m):
    return [(x, y) for x in range(1 << m) for y in range(1 << m)
            if x != y and included(x, y)]


def valid(summary, pairs):
    return all(not included(summary[x], summary[y]) for x, y in pairs)


def symmetric(summary, m):
    count = Counter((x.bit_count(), summary[x]) for x in range(1 << m))
    return len(count) == m + 1


def exhaust(m, b):
    pairs = strict_pairs(m)
    valid_count = symmetric_count = 0
    for summary in product(range(1 << b), repeat=1 << m):
        if valid(summary, pairs):
            valid_count += 1
            symmetric_count += symmetric(summary, m)
    return valid_count, symmetric_count


def one_spare(m, split):
    rank = m // 2
    top = m + 1
    return tuple(top - x.bit_count() - (x.bit_count() > rank or
                 (x.bit_count() == rank and x in split))
                 for x in range(1 << m))


if __name__ == "__main__":
    for m, b in ((2, 2), (3, 2)):
        totals = exhaust(m, b)
        print(f"m={m} b={b} valid={totals[0]} symmetric={totals[1]}")
        if m == 3:
            assert totals == (2, 2)
        else:
            assert totals[0] > totals[1]
    m = 6
    rank = m // 2
    layer = [x for x in range(1 << m) if x.bit_count() == rank]
    pairs = strict_pairs(m)
    # Check every split on four distinguished points of the middle layer.
    for membership in product((False, True), repeat=4):
        split = {x for x, present in zip(layer, membership) if present}
        summary = one_spare(m, split)
        assert valid(summary, pairs)
        assert symmetric(summary, m) == (not split)
    print("All 16 selected m=6 middle-layer splits passed.")
