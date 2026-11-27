"""Check the anchor, actual permutation files, critical clauses and simultaneous edits."""

from collections import Counter
from itertools import pairwise, permutations
from random import Random

from simple_permutation_successor import coloring_dimacs, simple
from single_lane_sat import ANCHOR, BLUE_GAPS, RED_GAP, render_lists, site

BOUNDARY = RED_GAP + BLUE_GAPS[0] + BLUE_GAPS[1]


def anchor_audit():
    edges = set(pairwise(range(len(ANCHOR)))) - {RED_GAP}
    edges.update(set(pairwise(ANCHOR)) - set(BLUE_GAPS))
    neighbors = [set() for _ in ANCHOR]
    for a, b in edges:
        neighbors[a].add(b)
        neighbors[b].add(a)
    row = [-1] * len(ANCHOR)
    counts = Counter()
    canonical = None

    def search():
        nonlocal canonical
        options = [
            (set(range(3)) - {row[j] for j in neighbors[i]}, i)
            for i, color in enumerate(row)
            if color == -1
        ]
        if not options:
            boundary = tuple(row[i] for i in BOUNDARY)
            counts[boundary] += 1
            if boundary == (1, 0, 2, 1, 2, 1):
                canonical = tuple(row)
            return
        colors, v = min(
            options, key=lambda item: (len(item[0]), -len(neighbors[item[1]]))
        )
        for color in colors:
            row[v] = color
            search()
        row[v] = -1

    search()
    assert simple(ANCHOR)
    assert counts == {
        tuple(perm[v] for v in (1, 0, 2, 1, 2, 1)): 8 for perm in permutations(range(3))
    }
    assert canonical is not None
    return canonical


def make_order(m, switches=()):
    odd = [site(j) for j in range(1, m + 1, 2)]
    even = [site(j) for j in range(2, m + 1, 2)]
    for j in switches:
        pos = j // 2 - 1
        even[pos - 1], even[pos] = even[pos], even[pos - 1]
    return render_lists(m, odd, even)


def centers(m):
    return tuple(j for j in range(6, m - 2, 2) if (j + m + 1) % 3 == 0)


def spliced_row(anchor, m, j):
    strip = tuple((i - 1 if i <= j else 2 + m - i) % 3 for i in range(1, m + 1))
    return anchor[: RED_GAP[1]] + strip + anchor[RED_GAP[1] :]


def bad_edges(order, row):
    return {
        tuple(sorted((a, b)))
        for path in (range(len(order)), order)
        for a, b in pairwise(path)
        if row[a] == row[b]
    }


def check_physical_edit(order, row, edge):
    lines = coloring_dimacs(order).splitlines()
    # Pick Z=false, so among the two copies only the +Z copy can fail.
    flags = {3 * v + col + 1 for v, col in enumerate(row)}

    def satisfied(clause):
        return any((abs(x) in flags) == (x > 0) for x in clause)

    clauses = [tuple(map(int, line.split()[:-1])) for line in lines[1:]]
    failures = [i for i, clause in enumerate(clauses) if not satisfied(clause)]
    assert len(failures) == 1
    i = failures[0]
    first, second, pin = clauses[i]
    assert first < 0 and second < 0 and pin == 3 * len(order) + 1
    assert set(edge) == {(-first - 1) // 3, (-second - 1) // 3}
    width = 1 + len(str(pin))
    original = lines[i + 1]
    edited_field = original[:width].replace(b"-", b" ")
    changed = edited_field + original[width:]
    assert (
        len(changed) == len(original)
        and sum(a != b for a, b in zip(changed, original)) == 1
    )
    assert satisfied(tuple(map(int, changed.split()[:-1])))


def audit():
    anchor = anchor_audit()
    rng = Random(707)
    total_repairs = 0
    for m in range(2, 81):
        base = make_order(m)
        assert simple(base)
        longer = make_order(m + 1)
        new = site(m + 1)
        assert tuple(v - (v > new) for v in longer if v != new) == base
        critical = set()
        for cut in range(2, m - 1):
            row = spliced_row(anchor, m, cut)
            failed = bad_edges(base, row)
            assert len(failed) == 1
            critical.update(failed)
            if m in (8, 17, 32):
                check_physical_edit(base, row, next(iter(failed)))
        assert len(critical) >= 2 * (m - 3) // 3
        edits = centers(m)
        if m <= 36:
            masks = range(1, 1 << len(edits))
        else:
            masks = {1 << i for i in range(len(edits))}
            masks.update(rng.randrange(1, 1 << len(edits)) for _ in range(10))
        for mask in masks:
            active = tuple(j for i, j in enumerate(edits) if mask >> i & 1)
            positive = make_order(m, active)
            assert simple(positive)
            assert sum(a != b for a, b in zip(positive, base)) == 2 * len(active)
            for cut in active:
                assert not bad_edges(positive, spliced_row(anchor, m, cut))
                total_repairs += 1
    print(
        "18-point anchor: 48 colorings with exactly the six required boundary patterns."
    )
    print("Literal growth and simplicity verified at every strip size 2 through 80.")
    print(
        f"Verified {total_repairs:,} positive witnesses on the actual simple permutations."
    )


if __name__ == "__main__":
    audit()
