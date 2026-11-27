"""Check prefix lifetime bases and the extremal counter stream."""

from itertools import combinations, permutations, product
from math import comb
from random import Random


def masks(v, p):
    return [sum(1 << i for i in subset) for k in range(p + 1)
            for subset in combinations(range(v), k)]


def select(assignments, monomials, lifetime):
    pivots = {}
    saved = []
    for a in sorted(assignments, key=lifetime.__getitem__, reverse=True):
        row = sum(1 << i for i, mask in enumerate(monomials) if a & mask == mask)
        while row:
            i = row.bit_length() - 1
            if i not in pivots:
                pivots[i] = row
                saved.append(a)
                break
            row ^= pivots[i]
    return saved


def check_order(v, p, lifetime):
    monomials = masks(v, p)
    saved = select(range(len(lifetime)), monomials, lifetime)
    assert len(saved) <= sum(comb(v, k) for k in range(p + 1))
    for mask in monomials:
        signs = mask
        while True:
            scores = [t for a, t in enumerate(lifetime) if a & mask == signs]
            kept = [lifetime[a] for a in saved if a & mask == signs]
            assert kept and max(kept) == max(scores)
            if signs == 0:
                break
            signs = (signs - 1) & mask


def count_wire_snapshots(data, p):
    row = [True] + [False] * (p + 1)
    for bit in data:
        row = [True] + [high or (bit and low) for low, high in zip(row, row[1:])]
    return row


def test_counter(v, p):
    witnesses = set()
    for a in range(1 << v):
        row = count_wire_snapshots([(a >> i) & 1 for i in range(v)], p)
        for r in range(p+1):
            assert (not row[r+1]) == (a.bit_count() <= r)
    for s in masks(v, p):
        r = s.bit_count()
        possible = [a for a in range(1 << v) if a & s == s and a.bit_count() <= r]
        assert possible == [s]
        witnesses.add(s)
    assert len(witnesses) == sum(comb(v, i) for i in range(p + 1))


def audit_single_threshold(v, p):
    # Bitsets of cube points satisfying a query with exactly p pinned bits.
    cubes = []
    for positions in combinations(range(v), p):
        for signs in product(range(2), repeat=p):
            cube = sum(1 << a for a in range(1 << v)
                       if all(((a >> i) & 1) == s for i, s in zip(positions, signs)))
            cubes.append(cube)
    inf = 1 << v
    largest_min_cover = 0
    for family in range(1 << (1 << v)):
        required = [c for c in cubes if c & family]
        best = inf
        subset = family
        while True:
            if all(c & subset for c in required):
                best = min(best, subset.bit_count())
            if not subset:
                break
            subset = (subset - 1) & family
        largest_min_cover = max(largest_min_cover, best)
    largest_irredundant = 0
    for k in range(1, min(1 << v, len(cubes)) + 1):
        for candidate in combinations(cubes, k):
            seen = shared = 0
            for c in candidate:
                shared |= seen & c
                seen |= c
            if all(c & ~shared for c in candidate):
                largest_irredundant = k
                break
        else:
            break
    assert largest_min_cover == largest_irredundant


def audit_two_thresholds(v, p, expected):
    cubes = [sum(1 << a for a in range(1 << v)
                 if all(((a >> i) & 1) == bit for i, bit in zip(positions, signs)))
             for positions in combinations(range(v), p)
             for signs in product(range(2), repeat=p)]
    after = []
    for family in range(1 << (1 << v)):
        exposed = 0
        for cube in cubes:
            restricted = cube & family
            if restricted.bit_count() == 1:
                exposed |= restricted
        after.append(family ^ exposed)
    optimum = max(family.bit_count() for family, residue in enumerate(after)
                  if not after[residue])
    assert optimum == expected


def audit_equal_verdicts(v):
    weight_two = [x for x in range(1 << v) if x.bit_count() == 2]
    full = (1 << v) - 1
    digit_rows = [sum(((i >> b) & 1) << i for i in range(v))
                  for b in range((v - 1).bit_length())]
    small = [0, full, *digit_rows, *(full ^ x for x in digit_rows)]
    for mask in masks(v, 2):
        sub = mask
        while True:
            forced_hits = [x for x in weight_two if x & mask == sub]
            assert forced_hits and any(x & mask == sub for x in small)
            if mask.bit_count() == 2 and sub == mask:
                assert forced_hits == [mask]
            if sub == 0:
                break
            sub = (sub - 1) & mask


def audit_fractional(v, p):
    tight = [x for x in range(1 << v) if x.bit_count() == p]
    for mask in masks(v, p):
        sub = mask
        while True:
            covered = sum(x & mask == sub for x in tight)
            assert covered >= 1
            if mask.bit_count() == p and sub == mask:
                assert covered == 1
            free_count = 1 << (v - mask.bit_count())
            assert (1 << p) * free_count >= 1 << v
            if sub == 0:
                break
            sub = (sub - 1) & mask


if __name__ == "__main__":
    for dim in range(1, 4):
        for width in range(dim + 1):
            audit_single_threshold(dim, width)
    for dim, width, optimum in [(3, 1, 4), (3, 2, 6), (4, 1, 5), (4, 2, 10), (4, 3, 14)]:
        audit_two_thresholds(dim, width, optimum)
    for dim in range(2, 10):
        for width in range(1, dim // 2 + 1):
            audit_fractional(dim, width)
    for dim in range(4, 12):
        audit_equal_verdicts(dim)
    cases = 0
    for order in permutations(range(8)):
        check_order(3, 2, order)
        cases += 1
    rng = Random(41)
    for _ in range(120):
        # Extra high bits of the assignment here are unpinnable auxiliaries.
        check_order(4, rng.randrange(5), [rng.randrange(12) for _ in range(64)])
        cases += 1
    for v in range(1, 10):
        for p in range(v + 1):
            test_counter(v, p)
    print(f"{cases:,} lifetime orders and preorders checked, including auxiliary bits")
    print("all counter thresholds and private support witnesses checked through v=9")
