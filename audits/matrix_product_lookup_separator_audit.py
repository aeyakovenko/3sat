"""Finite checks of the matrix-unit graph, its spectrum and its cut bound."""

from itertools import product
from random import Random


def check(d, rng):
    n = 3 * d * d

    def vertex(color, i, j):
        return color * d * d + i * d + j

    neighbors = [set() for _ in range(n)]
    completions = {}
    for i, j, k in product(range(d), repeat=3):
        triangle = [vertex(0, i, j), vertex(1, j, k), vertex(2, k, i)]
        for a in triangle:
            for b in triangle:
                if a != b:
                    assert (a, b) not in completions
                    completions[a, b] = next(c for c in triangle if c not in (a, b))
                    neighbors[a].add(b)
    assert all(len(row) == 2 * d for row in neighbors)
    assert all(sum(t == c for t in completions.values()) == 2 * d for c in range(n))

    # A³ - d² A = 2d J. Together with symmetry and the constant direction
    # this verifies |lambda| <= d for every unnormalized nonconstant mode.
    for a in range(n):
        walks = [0] * n
        for b in neighbors[a]:
            for c in neighbors[b]:
                for target in neighbors[c]:
                    walks[target] += 1
        assert all(walks[t] - d * d * (t in neighbors[a]) == 2 * d for t in range(n))

    if n <= 12:
        # For each X use the largest possible zero-edge Y. Smaller Y's only
        # strengthen x+y+3xy/N <= N.
        neighborhood_masks = [sum(1 << j for j in row) for row in neighbors]
        for mask in range(1 << n):
            neighbor_mask = 0
            for i in range(n):
                if (mask >> i) & 1:
                    neighbor_mask |= neighborhood_masks[i]
            x, y = mask.bit_count(), n - neighbor_mask.bit_count()
            assert n * (x + y) + 3 * x * y <= n * n

    for _ in range(400):
        left, right = rng.getrandbits(n), rng.getrandbits(n)
        x, y = left.bit_count(), right.bit_count()
        crossing = [c for (u, v), c in completions.items() if (left >> u) & (right >> v) & 1]
        missing = len(set(crossing))
        edge_count = len(crossing)
        assert edge_count <= 2 * d * missing
        gap = 2 * d * x * y - n * edge_count
        if gap > 0:
            assert gap * gap <= d * d * x * (n - x) * y * (n - y)

    print(f"d={d}: {n} vertices, {len(completions)} directed edges; spectrum and cuts verified")


if __name__ == "__main__":
    random = Random(20261125)
    for dimension in range(1, 6):
        check(dimension, random)
