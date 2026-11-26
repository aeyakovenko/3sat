"""Reproduce four-tip pattern minimality and positive-instance neighbors on full orders.

Run from the research repo, whose existing modules render the 18-point anchor and seven-triangle tiles.
"""

from itertools import pairwise, permutations, product
from random import Random

from one_point_strip_audit import anchor_audit, bad_edges
from simple_permutation_successor import simple
from single_lane_sat import compile_lane, extend_coloring, site


def local_blockers(k):
    rows = set()
    for y in product(range(3), repeat=k + 1):
        if any(a == b for a, b in pairwise(y)):
            continue
        rows.add(tuple(3 - a - b for a, b in pairwise(y)))
    return {
        p
        for p in permutations(range(k))
        if not any(all(z[a] != z[b] for a, b in pairwise(p)) for z in rows)
    }


def plant_order(n, rng):
    colors = [rng.randrange(3)]
    for _ in range(n - 1):
        colors.append(rng.choice([c for c in range(3) if c != colors[-1]]))
    while True:
        left = list(range(n))
        q = []
        while left:
            eligible = [v for v in left if not q or colors[q[-1]] != colors[v]]
            if not eligible:
                break
            v = rng.choice(eligible)
            left.remove(v)
            q.append(v)
        if not left:
            return tuple(q), tuple(colors)


def edge(u, v):
    return min(u, v), max(u, v)


def make_blocker(q, block, window, tips, inv):
    # Read the old contents of the source and destination slots before filling either.
    required = [tips[block + t] for t in (1, 0, 3, 2)]
    pool = {inv[v] for v in required} | set(range(window, window + 4))
    spare_values = sorted({q[p] for p in pool} - set(required))
    spare_slots = sorted(pool - set(range(window, window + 4)))
    edit = dict(zip(range(window, window + 4), required)) | dict(
        zip(spare_slots, spare_values)
    )
    assert len(pool) <= 8 and sorted(edit.values()) == sorted(q[p] for p in pool)
    return pool, edit


def check_negative(q, edits, blocks, tips):
    v = list(q)
    for edit in edits:
        for pos, val in edit.items():
            v[pos] = val
    assert sorted(v) == list(range(len(q))) and simple(v)
    es = {edge(i, i + 1) for i in range(len(q) - 1)} | {
        edge(i, j) for i, j in pairwise(v)
    }
    for block in blocks:
        local = tips[block : block + 4]
        for z in local:
            assert {edge(z - 1, z), edge(z, z + 1), edge(z - 1, z + 1)} <= es
        assert all(edge(local[i], local[j]) in es for i, j in ((1, 0), (0, 3), (3, 2)))


def audit_one(q, colors, tips, rng):
    size = len(tips)
    begin = min(q.index(t) for t in tips)
    assert (
        set(q[begin : begin + size]) == set(tips)
        and not bad_edges(q, colors)
        and simple(q)
    )
    inv = {v: i for i, v in enumerate(q)}
    blocks = list(range(2, size - 5, 4))
    windows = [begin + i for i in range(2, size - 5, 4)]
    rng.shuffle(windows)
    pairs = []
    for block, window in zip(blocks, windows):
        pool, edit = make_blocker(q, block, window, tips, inv)
        pairs.append((pool, edit, block))
        check_negative(q, [edit], [block], tips)
    used = set()
    packed = []
    for pool, edit, block in pairs:
        if pool.isdisjoint(used):
            used |= pool
            packed.append((edit, block))
    assert 9 * len(packed) >= len(blocks)
    check_negative(q, [edit for edit, _ in packed], [b for _, b in packed], tips)
    for _ in range(5):
        read = set(rng.sample(range(begin, begin + size), len(blocks) - 1))
        block = next(
            b for b in blocks if all(inv[tips[b + i]] not in read for i in range(4))
        )
        window = next(w for w in windows if all(w + i not in read for i in range(4)))
        pool, edit = make_blocker(q, block, window, tips, inv)
        assert pool.isdisjoint(read)
        check_negative(q, [edit], [block], tips)
    return len(pairs), len(packed)


def audit():
    assert all(not local_blockers(n) for n in range(1, 4))
    assert local_blockers(4) == {(1, 0, 3, 2), (2, 3, 0, 1)}
    rng = Random(417)
    anchor = anchor_audit()
    cases = repairs = packed = far = 0
    for n in (1, 2, 3, 5, 8, 12, 15, 21):
        for _ in range(2):
            p, source_colors = plant_order(n, rng)
            order = compile_lane(p)
            witness = extend_coloring(p, source_colors, anchor)
            tips = [site(2 + 2 * i) for i in range(7 * (n + 6))]
            native = list(order)
            # A random derangement within each color class preserves the full blue color sequence.
            begin = min(native.index(t) for t in tips)
            for a in range(3):
                slots = [
                    i
                    for i in range(begin, begin + len(tips))
                    if witness[native[i]] == a
                ]
                rng.shuffle(slots)
                if slots:
                    vals = [native[i] for i in slots]
                    shift = 1 if len(slots) > 1 else 0
                    for i, x in zip(slots, vals[shift:] + vals[:shift]):
                        native[i] = x
            assert sum(x != y for x, y in zip(native, order)) >= len(tips) - 3
            far += 1
            for q in (order, tuple(native)):
                a, b = audit_one(q, witness, tips, rng)
                cases += 1
                repairs += a
                packed += b
    print(
        f"{cases} full positive orders, including {far} far instances; {repairs} individual blockers, "
        f"{packed} disjoint blockers simultaneously implanted, and {5 * cases} adaptive avoidance checks."
    )
    print(
        "Exactly two blocking orders through four tips, both on four tips and reversals of each other."
    )


if __name__ == "__main__":
    audit()
