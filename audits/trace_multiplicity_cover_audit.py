"""Audit fixed-schedule recovery and sparse covers of fair-coin trace distributions."""

from itertools import combinations, product
from math import comb


def rank_mod_three(matrix):
    rows = [[v % 3 for v in row] for row in matrix]
    rank = 0
    for j in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = rows[rank][j]
        rows[rank] = [(inverse * v) % 3 for v in rows[rank]]
        for i in range(rank + 1, len(rows)):
            multiplier = rows[i][j]
            rows[i] = [(v - multiplier * p) % 3
                       for v, p in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def minimum_cover(matrix):
    """Find the least number of columns spanning the constant one vector."""
    width = len(matrix[0])
    for size in range(1, width + 1):
        for subset in combinations(range(width), size):
            for coefficients in product((1, 2), repeat=size):
                if all(sum(a * row[j] for j, a in zip(subset, coefficients)) % 3 == 1
                       for row in matrix):
                    return size
    raise AssertionError("no unit cover exists")


def check_small_distributions():
    # A fair two-bit tape gives four tapes. Every such row is realizable.
    rows = [(a, b, 4 - a - b) for a in range(5) for b in range(5 - a)]
    histogram = [0] * 4
    for matrix in product(rows, repeat=3):
        cover = minimum_cover(matrix)
        assert cover <= rank_mod_three(matrix)
        histogram[cover] += 1
    assert minimum_cover(((0, 4), (1, 3), (2, 2))) == 2
    return histogram


def check_program():
    # Locations 0,1,2 contain a, b, 1-b. Return whether the optional
    # units x (when a=1) and NOT x (when b=1) are jointly satisfiable.
    accepting_count = 0
    for a, b in product((0, 1), repeat=2):
        memory = [a, b, 1 - b]
        counts = [0, 0]
        accepts = [0, 0]
        for tape in range(4):
            order = a ^ (tape & 1)
            addr = 1 + order
            result = not (a and (memory[addr] ^ order))
            assert result == (not (a and b))
            counts[order] += 1
            accepts[order] += int(result)
        assert counts == [2, 2]
        assert 2 * accepts[0] % 3 == (not (a and b))
        accepting_count += accepts[0]
    return accepting_count


def check_rare_exceptions():
    for width in range(2, 12):
        for k in range(1, 6):
            matrix = [[4**k - 1] + [int(i == j) for j in range(width)]
                      for i in range(width)]
            assert rank_mod_three(matrix) == width
            for i, row in enumerate(matrix):
                assert [v % 3 for v in row] == [0] + [int(i == j) for j in range(width)]
                assert sum(row) == 4**k
    return 50


def check_ternary_digits():
    matrix = ((1, 0, 3), (1, 1, 2), (2, 0, 2))
    assert minimum_cover(matrix) == 3
    assert all((row[0] ** 2) % 3 == 1 for row in matrix)
    checked = 0
    for e in range(1001):
        all_zero = 1
        for j in range(5):
            k = 3**j
            digit = comb(e, k) % 3
            assert digit == (e // k) % 3
            all_zero = all_zero * (1 - digit**2) % 3
            assert bool(all_zero) == (e % (3*k) == 0)
            checked += 1
    return checked


if __name__ == "__main__":
    counts = check_small_distributions()
    print(f"{sum(counts)} three-row channels; least cover sizes 1, 2, 3: {counts[1:]}")
    print(f"Masked-address program: {check_program()} accepting tapes in the selected fibers")
    print(f"{check_rare_exceptions()} rare-exception channels of full modular rank")
    print(f"{check_ternary_digits()} ternary digit and zero-product tests")
