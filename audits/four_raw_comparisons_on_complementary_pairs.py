"""Exact support of four raw guards and the resulting marked-leaf recurrence."""

from itertools import combinations, product

import numpy as np


def minimal_masks(masks):
    # The aim is an empty intersection. A superset is weaker than its subset.
    minimal = []
    for mask in sorted(set(masks), key=int.bit_count):
        if not any((mask & small) == small for small in minimal):
            minimal.append(mask)
    return minimal


def raw_bound():
    targets = [(p, q, 15 - p, 15 - q) for p, q in product(range(4, 12), repeat=2)]
    negatives = [row for row in product(range(4, 12), repeat=4)
                 if (row[0] & row[2]) or (row[1] & row[3])]
    files = targets + negatives
    columns = list(np.asarray(files).T) + [np.full(len(files), v) for v in range(16)]
    positive = (1 << len(targets)) - 1
    universe = (1 << len(files)) - 1
    guards = set()
    for a, b in combinations(columns, 2):
        for test in (a == b, a < b, b < a, (a ^ 8) < (b ^ 8), (b ^ 8) < (a ^ 8)):
            bits = int.from_bytes(np.packbits(test, bitorder='little').tobytes(), 'little')
            for passed in (bits, bits ^ universe):
                if (passed & positive).bit_count() >= 2:
                    guards.add((passed & positive, passed >> len(targets)))
    easy = 0
    for i, j in combinations(range(len(targets)), 2):
        pair = (1 << i) | (1 << j)
        eligible = [n for p, n in guards if (p & pair) == pair]
        common = (1 << len(negatives)) - 1
        for mask in eligible:
            common &= mask
        if common:
            easy += 1
            continue
        single = minimal_masks(eligible)
        double = minimal_masks(a & b for a in single for b in single)
        assert all(a & b for a in double for b in double)
    assert (len(negatives), len(guards), easy) == (3772, 195, 1336)
    print(f'{len(guards)} guards and {len(negatives)} negatives exclude all 2,016 target pairs.')


def marked_tree_bound(w1, w2):
    # A subtree carrying a rejection cannot be an accepting terminal.
    full, marked = 1, 0
    for weight in (8, w2, w1):
        full, marked = max(weight, 2 * full), full + marked
    return full + marked


if __name__ == '__main__':
    raw_bound()
    assert marked_tree_bound(36, 18) == 63
    assert marked_tree_bound(38, 16) == 63
    print('If one- and two-comparison capacities are at most 36 and 18, the tree covers at most 63 targets.')
