"""Exact affine-cover number of three disjoint nonzero binary triples.

Each coordinate ranges over F_2^3 minus zero, identified with the masks
1,...,7. A plane with normal a requires dot(a,x)=1. Every rejecting-zero
affine flat is contained in such a plane (separate its offset from its
direction space). Apply this to each coordinate projection of a product-
domain flat, so it suffices to cover with products of planes.

Run: python three_clause_flat_cover_audit.py
"""

from collections import Counter
from itertools import combinations_with_replacement, product
from math import comb


LABELS = range(1, 8)
BOXES = (
    (1, 6, 6), (2, 7, 7), (6, 5, 3), (5, 6, 7),
    (2, 5, 2), (5, 4, 6), (1, 3, 4), (3, 3, 3),
    (4, 2, 1), (7, 1, 5), (6, 7, 2), (3, 4, 4),
)


def covers(a, x):
    return (a & x).bit_count() % 2


def audit():
    histogram = Counter(
        sum(all(covers(a, x) for a, x in zip(box, point)) for box in BOXES)
        for point in product(LABELS, repeat=3)
    )
    assert histogram == {1: 80, 2: 149, 3: 75, 4: 33, 5: 4, 6: 1, 7: 1}
    print(f"12 boxes cover all 343 points, with coverage histogram {sorted(histogram.items())}")

    # One block needs at least three planes. Each 2-block box appears in
    # exactly four first-coordinate slices, each of which needs three planes.
    assert all(sum(covers(a, x) for x in LABELS) == 4 for a in LABELS)
    pairs = list(combinations_with_replacement(LABELS, 2))
    assert all(any(not covers(a, x) and not covers(b, x) for x in LABELS) for a, b in pairs)
    assert 5 * 4 < 7 * 3
    # Six boxes suffice for two blocks: take the x=4 slice of the upper cover.
    two_blocks = [(b, c) for a, b, c in BOXES if covers(a, 4)]
    assert len(two_blocks) == 6
    assert all(any(covers(b, y) and covers(c, z) for b, c in two_blocks)
               for y, z in product(LABELS, repeat=2))

    # A six-box 2-block cover needs at least three boxes per slice.
    # Enumerate all one-coordinate multisets, independent of the upper cover.
    six_profiles = 0
    for normals in combinations_with_replacement(LABELS, 6):
        sizes = [sum(covers(a, x) for a in normals) for x in LABELS]
        if min(sizes) >= 3:
            assert len(set(normals)) == 6
            six_profiles += 1
    assert six_profiles == 7
    print(f"{six_profiles} of {comb(12, 6)} six-normal profiles qualify; all have distinct normals")

    # In eleven 3-block boxes some two second-coordinate normals coincide.
    # For every possible first-coordinate profile and every corresponding pair
    # of box positions, both boxes occur in a six-box first-coordinate slice.
    # That slice would contradict the six-normal test on the second coordinate.
    eleven_profiles = 0
    pair_checks = 0
    for normals in combinations_with_replacement(LABELS, 11):
        sizes = {x: sum(covers(a, x) for a in normals) for x in LABELS}
        if min(sizes.values()) < 6:
            continue
        assert sorted(sizes.values()) == [6] * 6 + [8]
        for i, a in enumerate(normals):
            for b in normals[:i]:
                assert any(size == 6 and covers(a, x) and covers(b, x) for x, size in sizes.items())
                pair_checks += 1
        eleven_profiles += 1
    assert pair_checks == 55 * eleven_profiles and eleven_profiles == 7
    print(f"{eleven_profiles} of {comb(17, 6)} eleven-normal profiles qualify; "
          f"all {pair_checks} position pairs meet in a minimum slice")
    assert all(sum(covers(a, x) and covers(b, x) for x in LABELS) == (4 if a == b else 2)
               for a, b in pairs)


if __name__ == "__main__":
    audit()
