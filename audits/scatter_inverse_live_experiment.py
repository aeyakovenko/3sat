"""Finite checks of adaptive exposure and the cycle-landmark lookup."""

from itertools import permutations
from math import comb, factorial


def adaptive_images(permutation, probes, seed):
    size = len(permutation)
    available = list(range(size))
    seen = []
    state = seed
    for step in range(probes):
        index = available.pop(state % len(available))
        value = permutation[index]
        seen.append(value)
        state = (step + 1) * (state + value + 1) + index
    return set(seen)


def cycle_landmarks(permutation, stride):
    visited = set()
    previous_landmark = {}
    for start in range(len(permutation)):
        if start in visited:
            continue
        cycle = []
        current = start
        while current not in visited:
            visited.add(current)
            cycle.append(current)
            current = permutation[current]
        if len(cycle) >= stride:
            marks = cycle[::stride]
            for offset, value in enumerate(marks):
                previous_landmark[value] = marks[offset - 1]
    return previous_landmark


def indexed_inverse(permutation, previous_landmark, target, stride):
    current = target
    for _ in range(stride + 1):
        if current in previous_landmark:
            current = previous_landmark[current]
            break
        successor = permutation[current]
        if successor == target:
            return current
        current = successor
    else:
        raise AssertionError("no landmark or return on the short cycle")
    for _ in range(stride):
        successor = permutation[current]
        if successor == target:
            return current
        current = successor
    raise AssertionError("target missing on preceding landmark segment")


def main():
    size = 7
    probes = 4
    targets = {1, 2, 5}
    counts = [0, 0, 0, 0]
    lookups = 0
    for permutation in permutations(range(size)):
        for seed in range(len(counts)):
            if targets <= adaptive_images(permutation, probes, seed):
                counts[seed] += 1
        for stride in range(1, size + 1):
            index = cycle_landmarks(permutation, stride)
            assert len(index) * stride <= 2 * size
            for target in range(size):
                source = indexed_inverse(permutation, index, target, stride)
                assert permutation[source] == target
                lookups += 1
    expected = factorial(size) * comb(probes, len(targets)) // comb(size, len(targets))
    assert counts == [expected] * len(counts)
    print(f"Adaptive fresh probes hit all {len(targets)} targets on "
          f"{expected}/{factorial(size)} permutations for each of {len(counts)} strategies.")
    print(f"{lookups} cycle-index lookups returned the correct inverse.")


if __name__ == "__main__":
    main()
