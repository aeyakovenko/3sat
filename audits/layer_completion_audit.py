"""Finite proof certificate for completion inside arbitrarily many partial four-site lifts."""

from collections import deque
from itertools import pairwise, product


def canonical(colors):
    names = {}
    return tuple(names.setdefault(c, len(names)) for c in colors)


TYPES = sorted({canonical(s) for s in product(range(3), repeat=4)})
INDEX = {s: i for i, s in enumerate(TYPES)}
DEFECT = 1 << INDEX[(0, 0, 0, 1)]
REPAIR = 1 << INDEX[(0, 1, 0, 0)]
EMPTY = sum(1 << i for i, (_, u, v, _) in enumerate(TYPES) if u != v)


def output_types(mask, state):
    red, u, v, head = state
    selected = [j for j in range(4) if mask >> j & 1]
    reachable = set()
    for colors in product(range(3), repeat=len(selected)):
        values = dict(zip(selected, colors))  # 0,1,2,3 are a,b,c,d
        paths = (
            [red, *colors],
            [u] + [values[j] for j in (2, 0) if j in values],
            [values[3], v] if 3 in values else [v],
            [values[1], head] if 1 in values else [head],
        )
        if any(x == y for path in paths for x, y in pairwise(path)):
            continue
        red_path, left, right, prefix = paths
        after = red_path[-1], left[-1], right[0], prefix[0]
        reachable.add(INDEX[canonical(after)])
    return sum(1 << i for i in reachable)


TRANSITIONS = [[output_types(mask, s) for s in TYPES] for mask in range(16)]


def prepend(mask, suffix):
    return sum(
        1 << i for i, outputs in enumerate(TRANSITIONS[mask]) if outputs & suffix
    )


def calculate():
    witnesses = {EMPTY: ()}
    pending = deque([EMPTY])
    while pending:
        suffix = pending.popleft()
        for m in range(16):
            result = prepend(m, suffix)
            if result not in witnesses:
                witnesses[result] = (m,) + witnesses[suffix]
                pending.append(result)
    return witnesses


def eligible(relation):
    return relation & DEFECT == 0 and relation & REPAIR != 0


def unpack(mask):
    digits = []
    while mask:
        digits.append(mask & 15)
        mask >>= 4
    return digits


def relation(mask):
    suffix = EMPTY
    for nibble in reversed(unpack(mask)):
        suffix = prepend(nibble, suffix)
    return suffix


def audit_cycle():
    from constant_point_lift_audit import lift
    from simple_permutation_successor import simple

    cycle = [
        (0x7171, 1),
        (0x7173, 2),
        (0x7177, 3),
        (0x717, 18),
        (0x40717, 17),
        (0x60717, 12),
        (0x61717, 16),
        (0x71717, 3),
    ]
    base = lift((2, 0, 3, 1), 1)
    full = base
    for _ in range(5):
        full = lift(full, 1)
    advancements = 0
    for i, (mask, bit) in enumerate(cycle):
        chosen = [v for v in full if v < len(base) or mask >> (v - len(base)) & 1]
        rank = {v: j for j, v in enumerate(sorted(chosen))}
        assert simple(tuple(rank[v] for v in chosen))
        # All colors of the three actual boundary vertices can be tried here.
        boundary = {canonical((v, u, v, h)) for v, u, h in product(range(3), repeat=3)}
        assert all(not relation(mask) >> INDEX[t] & 1 for t in boundary)
        assert not mask >> bit & 1
        updated = mask | (1 << bit)
        while updated & 15 == 15:
            updated >>= 4
            advancements += 1
        assert updated == cycle[(i + 1) % len(cycle)][0]
    assert advancements == 2


def audit():
    relations = calculate()
    assert len(TYPES) == 14 and len(relations) == 22
    assert max(map(len, relations.values())) == 3
    assert all(prepend(0, t) == t for t in relations)
    counts = []
    for last in range(4):
        counts.append(
            sum(
                eligible(prepend(15, t)) and eligible(prepend(15 ^ (1 << last), t))
                for t in relations
            )
        )
    assert counts == [0, 4, 0, 0]
    print(
        "14 four-port equality types, 22 suffix relations, shortest representatives of length ≤3."
    )
    print("Eligible completion counts for missing a,b,c,d:", counts)
    audit_cycle()
    print(
        "A simple negative eight-step one-point cycle advances twice and has a bounded local contradiction."
    )


if __name__ == "__main__":
    audit()
