"""Finite covering-code and entropy checks for lex-factor-responses.md."""

from collections import Counter, deque
from math import log2


def coset_weight_counts(parity_columns, check_bits):
    # Flipping one coordinate adds its parity-check column to the syndrome.
    # Breadth-first search therefore finds the least weight in every coset.
    distances = [-1] * (1 << check_bits)
    distances[0] = 0
    pending = deque([0])
    while pending:
        syndrome = pending.popleft()
        for column in parity_columns:
            neighbor = syndrome ^ column
            if distances[neighbor] < 0:
                distances[neighbor] = distances[syndrome] + 1
                pending.append(neighbor)
    assert -1 not in distances
    return Counter(distances)


def entropy(p):
    return -p * log2(p) - (1 - p) * log2(1 - p)


def bracket_decreasing_zero(value, lo, hi):
    assert value(lo) > 0 and value(hi) < 0
    for _ in range(45):
        mid = (lo + hi) / 2
        if value(mid) > 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


if __name__ == "__main__":
    identity = [1 << bit for bit in range(16)]
    extra = [0xA970, 0x78A6, 0x8956, 0xA0F7, 0xE36B, 0x17FC, 0x6DAA]
    counts = coset_weight_counts(identity + extra, 16)
    assert sum(counts.values()) == 1 << 16 and max(counts) == 7
    print("Coset-leader counts by weight:", sorted(counts.items()))

    c = 1 / 16
    lower = bracket_decreasing_zero(lambda x: entropy(c / x) + c / x - 1, 0.25, 0.32)
    upper = bracket_decreasing_zero(
        lambda x: entropy(c / x) + c * (x + 1 - c) / x - 1, 0.25, 0.32
    )
    assert 0.27521861 < lower[0] <= lower[1] < 0.27521863
    assert 0.29804614 < upper[0] <= upper[1] < 0.29804617
    print("First threshold:", lower)
    print("Second threshold:", upper)
