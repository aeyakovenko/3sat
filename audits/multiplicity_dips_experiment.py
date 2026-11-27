"""Check the exact finite maximum for clean trailing gaps of integer labels."""

from itertools import product


def qualifying_counts(labels):
    size = len(labels)
    counts = [0] * (size + 1)
    for z, value in enumerate(labels):
        previous = z - 1
        while previous >= 0 and labels[previous] > value:
            previous -= 1
        # A point qualifies precisely for the integer thresholds up to this one.
        last = (z - previous) // (value + 1)
        for threshold in range(1, last + 1):
            counts[threshold] += 1
    return counts


if __name__ == "__main__":
    arrays = 0
    for size in range(1, 9):
        for labels in product(range(4), repeat=size):
            counts = qualifying_counts(labels)
            assert all(counts[t] <= size // t for t in range(1, size + 1))
            arrays += 1
        for t in range(1, size + 1):
            example = [0 if (z + 1) % t == 0 else size for z in range(size)]
            assert qualifying_counts(example)[t] == size // t
    print(f"{arrays} arrays checked; floor bound attained for all tested lengths and thresholds")
