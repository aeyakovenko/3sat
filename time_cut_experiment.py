"""Exact primal and dual certificates for the 18-position time-cut packing.

All weights are multiplied by three. The checks use integer arithmetic and
the Python standard library; no linear-programming solver is needed.
"""

from fractions import Fraction
from itertools import combinations


N = 18
SCALE = 3

# (boundary, half-width, scaled weight), as in dynamic-cuts.md.
HALF = [
    (1, 1, 3), (2, 2, 3), (3, 1, 3), (4, 1, 1), (4, 4, 2),
    (5, 1, 2), (5, 5, 1), (6, 1, 1), (6, 2, 2), (7, 1, 2),
    (7, 2, 1), (8, 1, 1), (8, 2, 1), (8, 8, 1),
]
PACKING = [
    (c - h, c, c + h, weight)
    for c, h, weight in HALF + [(N - c, h, w) for c, h, w in HALF]
    + [(9, 1, 2), (9, 9, 1)]
]

# (i, j, scaled mass). Unlisted ordered pairs have mass zero.
DUAL = [
    (0, 1, 3), (0, 6, 1), (0, 9, 1),
    (1, 2, 3), (1, 3, 3),
    (2, 3, 3), (2, 5, 3), (2, 7, 2), (2, 10, 1),
    (3, 4, 3), (3, 6, 3),
    (4, 5, 3), (4, 7, 1), (4, 9, 1), (4, 10, 3),
    (5, 6, 3), (5, 7, 2), (5, 12, 5),
    (6, 7, 3), (6, 8, 1), (6, 9, 1), (6, 13, 2),
    (7, 8, 3), (7, 9, 1), (7, 10, 3), (7, 14, 2),
    (8, 9, 3), (8, 11, 2), (8, 13, 1), (8, 15, 1),
    (9, 10, 3), (9, 11, 1),
    (10, 11, 3), (10, 12, 2), (10, 14, 1), (10, 15, 2),
    (11, 12, 3), (11, 13, 1), (11, 14, 2), (11, 15, 1),
    (12, 13, 3), (12, 15, 3), (13, 14, 3),
    (14, 15, 3), (14, 16, 3), (15, 16, 3), (16, 17, 3),
]


def packing_score(n, cuts, scale):
    """Check pair congestion and return the scaled primal objective."""
    assert n >= 1 and scale > 0
    for left, boundary, right, weight in cuts:
        assert all(type(x) is int for x in (left, boundary, right, weight))
        assert 0 <= left < boundary < right <= n and weight >= 0
    for i, j in combinations(range(n), 2):
        load = sum(weight for left, boundary, right, weight in cuts
                   if left <= i < boundary <= j < right)
        assert load <= scale, (i, j, load)
    return sum(min(boundary - left, right - boundary) * weight
               for left, boundary, right, weight in cuts)


def dual_score(n, masses, scale):
    """Check every adjacent rectangle, including unequal interval lengths."""
    assert n >= 1 and scale > 0
    for i, j, mass in masses:
        assert all(type(x) is int for x in (i, j, mass))
        assert 0 <= i < j < n and mass >= 0
    for left, boundary, right in combinations(range(n + 1), 3):
        mass = sum(value for i, j, value in masses
                   if left <= i < boundary <= j < right)
        required = scale * min(boundary - left, right - boundary)
        assert mass >= required, (left, boundary, right, mass, required)
    return sum(mass for _, _, mass in masses)


def tree_scores(n):
    """Maximize the sum of min(child lengths) over all interval trees."""
    best = [0] * (n + 1)
    for length in range(2, n + 1):
        best[length] = max(best[left] + best[length - left]
                           + min(left, length - left)
                           for left in range(1, length))
    return best


if __name__ == "__main__":
    primal = packing_score(N, PACKING, SCALE)
    dual = dual_score(N, DUAL, SCALE)
    assert primal == dual == 107
    tree = tree_scores(N)[N]
    assert tree == 35 and primal > SCALE * tree
    print("18 positions: all 153 pair loads and 969 adjacent rectangles checked.")
    print(f"Exact packing optimum: {Fraction(primal, SCALE)}; "
          f"best interval tree: {tree}; gap: {Fraction(primal, SCALE) - tree}.")
