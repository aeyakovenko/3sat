"""Check communication ranks and the exact real Gram identity of permutation walks."""

from itertools import permutations, product

import numpy as np


def endpoint_matrix(width, owners):
    tables = tuple(permutations(range(width)))
    choices = [np.array(tuple(product(tables, repeat=owners.count(side))), dtype=np.int64)
               for side in (0, 1)]
    rows, columns = (len(bank) for bank in choices)
    position = np.zeros((rows, columns), dtype=np.int64)
    which = [0, 0]
    for side in owners:
        table = choices[side][:, which[side], :]
        index = np.arange(rows)[:, None] if side == 0 else np.arange(columns)[None, :]
        position = table[index, position]
        which[side] += 1
    return (position == 0).astype(np.int64)


def rank_mod(matrix, prime):
    work = matrix.copy() if matrix.shape[0] <= matrix.shape[1] else matrix.T.copy()
    pivot = 0
    for column in range(work.shape[1]):
        candidates = np.flatnonzero(work[pivot:, column])
        if len(candidates) == 0:
            continue
        chosen = pivot + candidates[0]
        work[[pivot, chosen]] = work[[chosen, pivot]]
        work[pivot] = (work[pivot] * pow(int(work[pivot, column]), -1, prime)) % prime
        factors = work[pivot + 1:, column:column + 1].copy()
        work[pivot + 1:] = (work[pivot + 1:] - factors * work[pivot]) % prime
        pivot += 1
        if pivot == work.shape[0]:
            break
    return pivot


def check(width, owners):
    runs = 1 + sum(a != b for a, b in zip(owners, owners[1:]))
    mat = endpoint_matrix(width, owners)
    for prime in (2, 3, 5):
        if width % prime:
            expected = 1 + (width - 1) ** (runs - 1)
        else:
            expected = 2 + sum((runs - gap) * (width - 2) ** gap
                               for gap in range(1, runs))
        actual = rank_mod(mat, prime)
        assert actual == expected, (width, owners, prime, actual, expected)
    # K = mF - 1. An integer identity checks the full centered singular spectrum.
    centered = width * mat - 1
    if centered.shape[0] > centered.shape[1]:
        centered = centered.T
    cubic = (centered @ centered.T) @ centered
    assert np.array_equal((width - 1) ** (runs - 2) * cubic, mat.size * centered)
    assert np.all(centered.sum(axis=0) == 0)
    assert np.all(centered.sum(axis=1) == 0)


def main():
    count = 0
    for width, max_layers in ((2, 7), (3, 5)):
        for layers in range(2, max_layers + 1):
            for suffix in product((0, 1), repeat=layers - 1):
                owners = (0,) + suffix
                if 1 in owners:
                    check(width, owners)
                    count += 1
    for width, owners in ((3, (0, 1, 0, 1, 0, 1)), (4, (0, 1, 0, 1))):
        check(width, owners)
        count += 1
    print(f"Checked {count} full layer partitions in characteristics 2, 3, 5.")
    print("The integer centered Gram identity held on every matrix.")


if __name__ == "__main__":
    main()
