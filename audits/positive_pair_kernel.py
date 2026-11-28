#!/usr/bin/env python3
"""Replay the signed-label kernel against the original clauses at every branch choice."""

from itertools import product
from random import Random


def normalize(clauses):
    unique = set()
    for clause in clauses:
        literals = set(clause)
        if not any(-literal in literals for literal in literals):
            unique.add(tuple(sorted(literals)))
    return sorted(unique)


def extract(clauses, n, block_width, cover=None):
    clauses = normalize(clauses)
    pairs = [c for c in clauses if len(c) == 2 and c[0] > 0]
    branches = len(pairs) if cover is None else len(cover)
    labels = 2 * branches + 1
    # The final label is permanently true. All others are pairs (j, polarity).
    forced = labels - 1
    support = [0] * (n + 1 + (0 if cover is None else branches))
    arcs, negatives = [], []
    if cover is None:
        for j, (left, right) in enumerate(pairs):
            support[left] |= 1 << (2 * j)
            support[right] |= 1 << (2 * j + 1)
    else:
        assert all(a in cover or b in cover for a, b in pairs)
        for j, v in enumerate(cover):
            support[v] |= 1 << (2 * j)
            tag = n + 1 + j
            support[tag] |= 1 << (2 * j + 1)
            negatives.append((v, tag))
            for a, b in pairs:
                if a == v:
                    support[b] |= 1 << (2 * j + 1)
                if b == v:
                    support[a] |= 1 << (2 * j + 1)
    for clause in clauses:
        if clause in pairs:
            continue
        if len(clause) == 1 and clause[0] > 0:
            support[clause[0]] |= 1 << forced
        elif all(x < 0 for x in clause):
            negatives.append(tuple(-x for x in clause))
        else:
            assert len(clause) == 2 and clause[0] < 0 < clause[1]
            arcs.append((-clause[0], clause[1]))
    # Fixpoint and SCC propagation give the same reachability sets.
    changed = True
    while changed:
        changed = False
        for u, v in arcs:
            joined = support[u] | support[v]
            if joined != support[v]:
                support[v] = joined
                changed = True

    groups = (labels + block_width - 1) // block_width
    block_mask = (1 << block_width) - 1
    marked = set()
    output = set()
    for negative in negatives:
        if not negative:
            output.add(())
            continue
        triple = (negative + (negative[-1],) * 2)[:3]
        slices = [
            [(j * block_width, (support[v] >> (j * block_width)) & block_mask)
             for j in range(groups) if (support[v] >> (j * block_width)) & block_mask]
            for v in triple
        ]
        marked.update(product(*slices))
    for key in marked:
        local_labels = [
            [off + i for i in range(block_width) if mask & (1 << i)] for off, mask in key
        ]
        for chosen in product(*local_labels):
            # Even label selects the left endpoint when the branch bit is 1.
            clause = {((r // 2) + 1) * (1 if r % 2 else -1) for r in chosen if r != forced}
            if not any(-literal in clause for literal in clause):
                output.add(tuple(sorted(clause)))
    return pairs, sorted(output)


def satisfied(clauses, assignment):
    def true(literal):
        return bool(assignment & (1 << (abs(literal) - 1))) == (literal > 0)
    return all(any(true(literal) for literal in clause) for clause in clauses)


def compare(clauses, n):
    # Test direct input semantics including duplicates, tautologies and empty clauses.
    assignments = [a for a in range(1 << n) if satisfied(clauses, a)]
    pairs, kernel = extract(clauses, n, 1)
    assert extract(clauses, n, 2) == (pairs, kernel)
    assert extract(clauses, n, 4) == (pairs, kernel)
    for choices in range(1 << len(pairs)):
        roots = [c[0 if choices & (1 << j) else 1] for j, c in enumerate(pairs)]
        pinmask = sum(1 << (v - 1) for v in set(roots))
        possible = any((a & pinmask) == pinmask for a in assignments)
        assert satisfied(kernel, choices) == possible, (clauses, choices, kernel)
    # A maximal matching supplies an explicit vertex cover of size at most 2*matching.
    cover = []
    for a, b in pairs:
        if a not in cover and b not in cover:
            cover.extend((a, b))
    # Delete redundant members to test small covers and edges internal to the cover.
    for v in cover.copy():
        remaining = [u for u in cover if u != v]
        if all(a in remaining or b in remaining for a, b in pairs):
            cover = remaining
    _, cover_kernel = extract(clauses, n, 2, cover)
    for choices in range(1 << len(cover)):
        possible = any(all(((a >> (v-1)) & 1) == ((choices >> j) & 1)
                           for j, v in enumerate(cover)) for a in assignments)
        assert satisfied(cover_kernel, choices) == possible, (clauses, choices, cover_kernel)
    return len(assignments) > 0


def check_intersection_bound():
    checked = 0
    for p in range(1, 5):
        for mask in range(1, 1 << (1 << p)):
            rows = [x for x in range(1 << p) if mask & (1 << x)]
            if any(not (mask & (1 << (x & y))) for j, x in enumerate(rows) for y in rows[:j]):
                continue
            distance = min(((x ^ y).bit_count() for j, x in enumerate(rows) for y in rows[:j]),
                           default=p+1)
            assert len(rows) <= 1 << (p // distance)
            checked += 1
    return checked


def main():
    menu = [(1, 2), (2, 3), (1,), (-3,), (-1, 2), (-2, 1),
            (-2, 3), (-3, 1), (-1, -2), (-1, -2, -3)]
    yes = sum(compare([c for j, c in enumerate(menu) if mask & (1 << j)], 3)
              for mask in range(1 << len(menu)))
    assert 0 < yes < 1 << len(menu)

    rng = Random(19385)
    extra = [[], [()], [(1, -1, 2), (1, 1), (-1, -1)],
             [(1, 2), (2, 1), (1, 2), (4, 5), (-1, -4, -5), (-3, 2), (-2, 3)]]
    for _ in range(180):
        clauses = []
        for _ in range(rng.randrange(18)):
            width = rng.choice([1, 2, 2, 3])
            row = rng.sample(range(1, 6), width)
            clauses.append(tuple(-v if width == 3 or rng.getrandbits(1) else v for v in row))
        extra.append(clauses)
    for clauses in extra:
        compare(clauses, 5)
    families = check_intersection_bound()
    print(f"{families} nonempty intersection-closed families on 1 through 4 coordinates")
    print(f"{1 << len(menu)} three-variable formulas ({yes} satisfiable), "
          f"{len(extra)} additional trials, all branch choices and three block widths agree")


if __name__ == "__main__":
    main()
