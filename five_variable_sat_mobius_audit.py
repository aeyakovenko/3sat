"""Exact covers by proper 3-clauses via signed inclusion-exclusion and cube symmetry."""

from itertools import combinations
from math import comb
from functools import lru_cache

import numpy as np


def faces(d, free_count):
    """Return the assignment masks of all free_count-dimensional cube faces."""
    result = []
    for free in combinations(range(d), free_count):
        free_mask = sum(1 << i for i in free)
        for fixed in range(1 << d):
            if fixed & free_mask == 0:
                result.append(sum(1 << x for x in range(1 << d)
                                  if (x & ~free_mask) == fixed))
    return result


def orbit_representatives(d):
    size = 1 << d
    point_maps = [[x ^ (1 << i) for x in range(size)] for i in range(d)]
    for i in range(d - 1):
        mask = 3 << i
        point_maps.append([x ^ mask if ((x >> i) & 3) in (1, 2) else x for x in range(size)])
    maps = []
    for perm in point_maps:
        images = [0] * (1 << size)
        for subset in range(1, len(images)):
            bit = subset & -subset
            images[subset] = images[subset ^ bit] | (1 << perm[bit.bit_length() - 1])
        maps.append(images)
    seen = bytearray(1 << size)
    for root in range(len(seen)):
        if seen[root]:
            continue
        orbit = [root]
        seen[root] = 1
        for element in orbit:
            for move in maps:
                image = move[element]
                if not seen[image]:
                    seen[image] = 1
                    orbit.append(image)
        yield root, len(orbit)


def census(d):
    # d is the whole-cube dimension; we tabulate all subsets of one slice.
    points = 1 << (d - 1)
    subsets = np.arange(1 << points, dtype=np.uint32)
    even = np.array([int(i).bit_count() % 2 == 0 for i in subsets])
    free_count = d - 3
    in_slice = np.zeros(len(subsets), dtype=np.int16)
    cross = in_slice.copy()
    for face in faces(d - 1, free_count):
        in_slice += ((subsets & face) == face)
    for face in faces(d - 1, free_count - 1):
        cross += ((subsets & face) == face)
    clause_count = comb(d, 3) * 8
    signed_counts = np.zeros(clause_count + 1, dtype=np.int64)
    reps = list(orbit_representatives(d - 1))
    assert sum(size for _, size in reps) == len(subsets)
    for x, size in reps:
        available = in_slice[x] + in_slice + cross[subsets & x]
        positive = np.bincount(available[even], minlength=len(signed_counts))
        negative = np.bincount(available[~even], minlength=len(signed_counts))
        signed_counts += (size if even[x] else -size) * (positive - negative)
    # Only the arbitrary-precision binomial transform may exceed a 64-bit integer.
    covers = [sum(int(weight) * comb(n, m) for n, weight in enumerate(signed_counts) if n >= m)
              for m in range(clause_count + 1)]
    assert all(0 <= count <= comb(clause_count, m) for m, count in enumerate(covers))
    assert covers[-1] == 1 and covers[:8] == [0] * 8
    return len(reps), covers


def exact_partitions(d):
    """Independent eight-clause census, selecting a disjoint face at the first hole."""
    size = 1 << d
    containing = [[] for _ in range(size)]
    for face in faces(d, d - 3):
        for i in range(size):
            if face >> i & 1:
                containing[i].append(face)

    @lru_cache(None)
    def visit(uncovered):
        if not uncovered:
            return 1
        pos = (uncovered & -uncovered).bit_length() - 1
        return sum(visit(uncovered ^ face) for face in containing[pos]
                   if face & uncovered == face)

    return visit((1 << size) - 1)


if __name__ == "__main__":
    for dimension in (4, 5):
        orbits, counts = census(dimension)
        assert counts[8] == exact_partitions(dimension)
        if dimension == 4:
            assert counts[8:10] == [272, 15936]  # Also obtained by direct nine-set enumeration.
        options = comb(dimension, 3) * 8
        minimal9 = counts[9] - (options - 8) * counts[8]
        print(f"d={dimension}, {orbits} first-slice orbits, {options} proper signed clauses")
        print(f"eight covers={counts[8]:,}; nine covers={counts[9]:,}; minimal nine={minimal9:,}")
        print(f"ten covers={counts[10]:,}; all nine-subsets={comb(options, 9):,}")
