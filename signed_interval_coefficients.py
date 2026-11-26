"""Reproduce the signed product and all small fixed-boundary counting identities."""

from collections import Counter
from itertools import pairwise, permutations, product
from math import lcm, prod

P = (0, 2, 1, 3, 5, 4)
Q = (2, 0, 3, 1)
TILE = (1, 4, 3, 5, 6, 0, 2)


def base_and_tips(signs):
    base = [0]
    tips = []
    for d in signs:
        tips.append((base[-1] - d) % 3)
        base.append((base[-1] + d) % 3)
    return base, tips


def value(order, signs):
    _, z = base_and_tips(signs)
    return prod(z[j] - z[i] for i, j in pairwise(order)) % 3


def copies(order, r):
    return tuple(len(order) * i + v for i in range(r) for v in order)


def squarefree_degree(order):
    n = len(order)
    a = [
        value(order, tuple(1 if mask >> i & 1 == 0 else -1 for i in range(n)))
        for mask in range(2**n)
    ]
    for i in range(n):
        for s in range(2**n):
            if not s >> i & 1:
                low, hi = a[s], a[s | 1 << i]
                a[s], a[s | 1 << i] = (low + hi) % 3, (low - hi) % 3
    return max((s.bit_count() for s, c in enumerate(a) if c), default=-1)


INCREMENT = (1, 2, 0, 4, 5, 3)
DOUBLE_ADD_ONE = (1, 5, 3, 4, 2, 0)


def transfer(order):
    rows = [[0, 0], [0, 0]]
    for signs in product((1, -1), repeat=len(order)):
        if not value(order, signs):
            continue
        y, z = base_and_tips(signs)
        for incoming in (0, 1):
            if z[order[0]] != incoming:
                rows[incoming][int(z[order[-1]] != y[-1])] += 1
    return tuple(map(tuple, rows))


def integer_tiles(target):
    if target <= 0:
        raise ValueError("expected a positive witness multiplier")
    tiles = []
    while target > 2:
        if target % 2 == 0:
            tiles.append(INCREMENT)
            target -= 1
        tiles.append(DOUBLE_ADD_ONE)
        target = (target - 1) // 2
    if target == 2:
        tiles.append(INCREMENT)
    return tiles


def audit_counts():
    matrices = {tile: transfer(tile) for tile in (INCREMENT, DOUBLE_ADD_ONE)}
    assert transfer((1, 2, 0, 3)) == ((0, 4), (0, 4))
    assert transfer(TILE) == ((0, 0), (0, 4))
    assert transfer(P) == ((16, 0), (8, 0))
    assert matrices[INCREMENT] == ((4, 0), (4, 4))
    assert matrices[DOUBLE_ADD_ONE] == ((4, 0), (4, 8))
    for target in range(1, 1001):
        tiles = integer_tiles(target)
        e = d = 1
        for tile in reversed(tiles):
            m = matrices[tile]
            e, d = m[0][0] * e + m[0][1] * d, m[1][0] * e + m[1][1] * d
        assert (e, d) == (4 ** len(tiles), 4 ** len(tiles) * target)
    for q, g, target in ((1, 2, 2), (0, 3, 4), (1, 1, 3), (0, 6, 1)):
        tiles = [P] * q + [tuple(range(g))] + integer_tiles(target)
        direct = []
        for tile in tiles:
            shift = len(direct)
            direct.extend(shift + v for v in tile)
        count = sum(
            bool(value(direct, row)) for row in product((1, -1), repeat=len(direct))
        )
        assert count == 2 * 16**q * 4 ** len(integer_tiles(target)) * target
    for bound in (5, 11, 50, 500):
        target = lcm(*range(1, bound + 1))
        tiles = integer_tiles(target)
        assert len(tiles) <= 2 * target.bit_length()
        assert all(target % k == 0 for k in range(1, bound + 1))
    print(
        "The two six-tip transfer tables, all multipliers 1..1,000 and four simultaneous modulus bounds pass."
    )


def audit():
    audit_counts()
    for r in (1, 2):
        p = copies(P, r)
        hits = 0
        for row in product((1, -1), repeat=len(p)):
            reduced = -row[0] * prod(
                (row[o + 1] + row[o + 2]) * (row[o + 4] + row[o + 5])
                for o in range(0, len(p), 6)
            )
            assert value(p, row) == reduced % 3
            hits += reduced % 3 != 0
        assert hits == 2 ** (4 * r) and squarefree_degree(p) == 2 * r + 1
    small = (1, 0, 2, 4, 3)
    assert squarefree_degree(small) == 2
    for n in range(2, 5):
        assert all(squarefree_degree(p) in (-1, n - 1) for p in permutations(range(n)))

    normalized = Counter()
    for row in product((1, -1), repeat=4):
        base, z = base_and_tips(row)
        if value(Q, row):
            assert z[Q[-1]] != base[-1]
            normalized[z[Q[0]]] += 1
    assert normalized == {1: 3, 2: 3}
    for r in (1, 2, 3):
        assert (
            sum(
                bool(value(copies(Q, r), row)) for row in product((1, -1), repeat=4 * r)
            )
            == 2 * 3**r
        )

    tile_counts = Counter()
    for row in product((1, -1), repeat=7):
        if value(TILE, row):
            y, z = base_and_tips(row)
            assert z[TILE[0]] == z[TILE[-1]] == 0
            assert row[5] % 3 == -y[-1] % 3
            tile_counts[y[-1], row[0]] += 1
    assert tile_counts == {(1, 1): 1, (1, -1): 1, (2, 1): 1, (2, -1): 1}
    print(
        "Signed product and degree checked for one and two six-tip blocks; no smaller top failure through four."
    )
    print(
        "All four-tip counts through three blocks and all 128 seven-tip sign vectors checked."
    )


if __name__ == "__main__":
    audit()
