"""Exhaustive binary rank-one mask counts for all row spaces up to 2 by 3."""

from itertools import combinations


def subspaces(dimension):
    for rank in range(dimension + 1):
        for pivots in combinations(range(dimension), rank):
            free = [(i, j) for i, p in enumerate(pivots)
                    for j in range(p + 1, dimension) if j not in pivots]
            for coefficients in range(1 << len(free)):
                basis = [1 << p for p in pivots]
                for k, (i, j) in enumerate(free):
                    if coefficients >> k & 1:
                        basis[i] |= 1 << j
                space = [0]
                for vector in basis:
                    space += [v ^ vector for v in space]
                yield frozenset(space)


def mask(u, v, width):
    return sum(v << (i * width) for i in range(u.bit_length()) if u >> i & 1)


def verify(rows, columns):
    masks = {mask(u, v, columns) for u in range(1, 1 << rows)
             for v in range(1, 1 << columns)}
    count = equality = 0
    seen = set()
    for space in subspaces(rows * columns):
        assert space not in seen
        seen.add(space)
        dims = []
        for i in range(rows):
            row_space = {w >> (i * columns) for w in space if w >> ((i + 1) * columns) == 0}
            dims.append(len(row_space).bit_length() - 1)
        dims.sort(reverse=True)
        assert sum(dims) == len(space).bit_length() - 1
        bound = sum((1 << i) * ((1 << size) - 1) for i, size in enumerate(dims))
        actual = len(space & masks)
        assert actual <= bound
        ferrers = sum(((1 << size) - 1) << (i * columns) for i, size in enumerate(dims))
        assert sum((w & ferrers) == w for w in masks) == bound
        count += 1
        equality += actual == bound
    return count, equality


if __name__ == "__main__":
    for shape in [(2, 2), (2, 3), (3, 2)]:
        total, sharp = verify(*shape)
        print(f"{shape[0]} by {shape[1]}: {total} subspaces, {sharp} attain their profile bound")
