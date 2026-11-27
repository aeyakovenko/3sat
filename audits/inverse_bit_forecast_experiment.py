"""Finite checks of the sequential Hamming ball and the swap coupling."""

from itertools import permutations, product
from math import comb


def sequential_ball() -> None:
    depth = 3
    for tree in product((0, 1), repeat=(1 << depth) - 1):
        counts = [0] * (depth + 1)
        for bits in product((0, 1), repeat=depth):
            node = 0
            errors = 0
            for bit in bits:
                errors += tree[node] != bit
                node = 2 * node + 1 + bit
            counts[errors] += 1
        assert counts == [comb(depth, i) for i in range(depth + 1)]
    print("All 128 predictors give the exact depth-three sequential Hamming ball.")


def forecast(oracle: tuple[int, ...], position: int) -> tuple[tuple[int, ...], set[int]]:
    # A deterministic sequential predictor, with one fresh forward query per bit.
    used = set()
    predictions = []
    prefix = 0
    for j in range(2):
        query = (3 * prefix + 2 * j + 1) % len(oracle)
        used.add(query)
        predictions.append((oracle[query] >> j) & 1)
        prefix |= ((position >> j) & 1) << j
    return tuple(predictions), used


def swap_check() -> None:
    size = 8
    runs = 0
    misses_both = 0
    counts = {}
    for auxiliary in permutations(range(size)):
        old = auxiliary.index(0)
        ghost_good = 0
        for position in range(size):
            real = list(auxiliary)
            real[old], real[position] = real[position], real[old]
            real = tuple(real)
            counts[real] = counts.get(real, 0) + 1
            assert real[position] == 0
            ghost_predictions, probes = forecast(auxiliary, position)
            ghost_good += ghost_predictions == ((position & 1), (position >> 1) & 1)
            if old not in probes and position not in probes:
                assert forecast(real, position) == (ghost_predictions, probes)
                misses_both += 1
            runs += 1
        assert ghost_good == 2  # One matching two-bit prefix, one free bit.
    assert len(counts) == 40320 and set(counts.values()) == {size}
    print(f"{runs} swaps produced the uniform permutation distribution; "
          f"{misses_both} runs missed both special positions.")


def check_full_scan() -> None:
    size = 4
    passed = 0
    for table in permutations(range(size)):
        honest = tuple(table.index(key) for key in range(size))
        for candidate in product(range(size), repeat=size):
            accepted = all(table[index] == key for key, index in enumerate(candidate))
            assert accepted == (candidate == honest)
            passed += accepted
    assert passed == 24
    print("Exactly the true response stream passed for all 24 four-item permutations.")


if __name__ == "__main__":
    sequential_ball()
    swap_check()
    check_full_scan()
