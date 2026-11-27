"""Finite checks for strict separator weights, two defaults and sparse markers."""

from itertools import combinations, permutations, product
from math import prod


def determinant(matrix):
    n = len(matrix)
    total = 0
    for cols in permutations(range(n)):
        inv = sum(cols[i] > cols[j] for i in range(n) for j in range(i + 1, n))
        total += (-1)**inv * prod(row[col] for row, col in zip(matrix, cols))
    return total


def check_weights():
    rows = [(1,) + row for row in product((0, 1), repeat=3)]
    systems = set()
    for basis in combinations(rows, 4):
        den = determinant(basis)
        if not den:
            continue
        for signs in product((-1, 1), repeat=4):
            weights = []
            for j in range(4):
                amended = [row[:j] + (target,) + row[j+1:] for row, target in zip(basis, signs)]
                weights.append(determinant(amended) * (1 if den > 0 else -1))
            assert all(abs(w) <= 4**2 for w in weights)
            values = [sum(x*w for x, w in zip(row, weights)) for row in rows]
            if all(values):
                systems.add(tuple(v > 0 for v in values))

    brute = set()
    for weights in product(range(-6, 7), repeat=4):
        values = [sum(x*w for x, w in zip(row, weights)) for row in rows]
        if all(values):
            brute.add(tuple(v > 0 for v in values))
    assert systems == brute and len(systems) == 104
    return len(systems)


def check_defaults_and_marker():
    defaults = 0
    for truth in product((0, 1), repeat=4):
        for cheap in product((False, True), repeat=4):
            hits = [sum(ok or expected == default for ok, expected in zip(cheap, truth))
                    for default in (0, 1)]
            assert sum(hits) == 4 + sum(cheap)
            assert 2 * max(hits) >= 4 + sum(cheap)
            defaults += 1
    markers = 0
    for table in product((0, 1), repeat=8):
        for prefix, last in product(range(4), range(2)):
            positives = [cand for cand in range(4) if table[2*cand + last]]
            hits = sum(cand == prefix for cand in positives)
            assert hits == table[2*prefix + last]
            markers += 1
    return defaults, markers


def check_outer_table():
    # For two sums, use the degree-one central parity polynomial on levels 0,1.
    tests = 0
    for x, y in product(range(16), repeat=2):
        z = (x & y).bit_count()
        shifted = ((y << 1) & 15) | (y >> 3)
        w = (x & shifted).bit_count()
        if max(z, w) > 1:
            continue
        for outer in product((-1, 1), repeat=4):
            v1, v2 = 1-2*z, 1-2*w
            four_times_value = sum(outer[2*i+j] * (1+(-1)**i*v1) * (1+(-1)**j*v2)
                                   for i, j in product((0, 1), repeat=2))
            assert four_times_value == 4*outer[2*(z % 2)+(w % 2)]
            tests += 1
    return tests


if __name__ == "__main__":
    thresholds = check_weights()
    defaults, markers = check_defaults_and_marker()
    central = check_outer_table()
    print(f"{thresholds} strict cube thresholds by exact determinants; {defaults} default tests; "
          f"{markers} one-marker decisions; {central} two-form outer compositions")
