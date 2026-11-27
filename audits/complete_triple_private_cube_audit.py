"""Exhaust the six-coordinate gap for private codimension-three cubes."""

from fractions import Fraction
from collections import defaultdict
from itertools import combinations, permutations, product
from math import comb
from random import Random

SIX = (1 << 6) - 1
EDGES = tuple(sum(1 << x for x in e) for e in combinations(range(6), 3))


def blocker_options(edge):
    """For every possible blocker B, encode all other edges failing to meet B."""
    options = []
    for block in range(64):
        if block & edge:
            continue
        uncovered = sum(
            1 << j for j, other in enumerate(EDGES) if other != edge and not other & block
        )
        options.append((block, uncovered))
    return sorted(options, key=lambda item: (item[0].bit_count(), item[0]))


def scaled_weight(block):
    return 60 // comb(3 + block.bit_count(), 3)


def best_blockers(family, options):
    for j, rules in enumerate(options):
        if family & (1 << j):
            block = next(block for block, uncovered in rules if not uncovered & family)
            yield EDGES[j], block


def check_worst_by_permutations(family, options):
    blockers = tuple(best_blockers(family, options))
    hits = 0
    for order in permutations(range(6)):
        pos = {v: i for i, v in enumerate(order)}
        successes = 0
        for edge, block in blockers:
            latest_edge = max(pos[v] for v in range(6) if edge & (1 << v))
            first_block = min(pos[v] for v in range(6) if block & (1 << v))
            successes += latest_edge < first_block
        assert successes <= 1
        hits += successes
    assert hits == 684


def check_cube_mass():
    """Independently sum the exact rational per-cube contribution for several n."""
    for n in range(3, 44):
        total = sum(Fraction(comb(n - 3, r), comb(r + 3, 3)) for r in range(n - 2))
        assert comb(n, 3) * total == 2**n - 1 - n - comb(n, 2)


def star_forest_dp(t):
    """Add labeled rows. Locked columns meet a degree-at-least-two row."""
    states = {(0, 0, 0): 1}
    for _ in range(t):
        new = defaultdict(int)
        for (locked, singleton, edges), multiplicity in states.items():
            for neighbors in range(1 << t):
                count = neighbors.bit_count()
                if neighbors & locked or count >= 2 and neighbors & singleton:
                    continue
                if count >= 2:
                    key = (locked | neighbors, singleton, edges + count)
                else:
                    key = (locked, singleton | neighbors, edges + count)
                new[key] += multiplicity
        states = new
    return sum(states.values()), max(edges for _, _, edges in states)


def check_small_forests():
    t = 4
    count = 0
    best = 0
    for table in range(1 << (t*t)):
        rows = [(table >> (t*i)) & ((1 << t)-1) for i in range(t)]
        cols = [sum((row >> j) & 1 for row in rows) for j in range(t)]
        if all(
            row.bit_count() <= 1 or cols[j] <= 1
            for row in rows for j in range(t) if row & (1 << j)
        ):
            count += 1
            best = max(table.bit_count(), best)
    assert (count, best) == star_forest_dp(t)
    count6, best6 = star_forest_dp(6)
    assert best6 == 10
    return count6


def full_projection(values, t):
    """Search the compulsory clauses combining one outside bit with two names."""
    for i, j in combinations(range(3), 2):
        for a, b in product(range(t), repeat=2):
            patterns = {(point[i] == a, point[j] == b, z) for point, z in values}
            if len(patterns) == 8:
                return True
    return False


def check_grid():
    t = 6
    beta = Fraction(8, 25)
    assert Fraction(2*t-1, t*t) < beta
    assert 3 * Fraction(10, 2*t*t) < 2*beta*(1-beta)
    assert Fraction(1, t**3) < 1-3*beta
    assert Fraction(1, t) < beta
    # Exhaust Boolean colorings of eight 3x3x3 blocks partitioning the 6-cube grid.
    points = list(product(range(t), repeat=3))
    balanced = 0
    for colors in range(256):
        values = []
        for point in points:
            block = sum((i >= 3) << j for j, i in enumerate(point))
            values.append((point, (colors >> block) & 1))
        mass = Fraction(sum(z for _, z in values), len(values))
        if beta <= mass <= 1-beta:
            balanced += 1
            assert full_projection(values, t)
    # Each signed coordinate indicator can be complemented independently.
    # Each of the 8 possible ordered signs still identifies exactly one grid point.
    for signs in product(range(2), repeat=3):
        for triple in points:
            hits = [point for point in points if all(
                (((point[d] == triple[d]) ^ signs[d]) == (1 ^ signs[d]))
                for d in range(3)
            )]
            assert hits == [triple]
    print(f"{balanced} balanced block colorings expose all eight forbidden projections")
    print(f"{8*len(points)} signed grid clauses have exactly their own private point")


def shatters(rows, support, b):
    counts = defaultdict(int)
    for row in rows:
        counts[row & support] += 1
    return len(counts) == 1 << support.bit_count() and min(counts.values()) > b


def surviving_supports(rows, n, b):
    return {s for s in range(1 << n) if shatters(rows, s, b)}


def check_split(rows, left, right, axis, n, b):
    parent = surviving_supports(rows, n, b)
    a, c = surviving_supports(left, n, b), surviving_supports(right, n, b)
    promoted = {s | (1 << axis) for s in a & c}
    assert not promoted & (a | c)
    assert (promoted | a | c) <= parent
    assert len(a) + len(c) <= len(parent)


def weighted_checks():
    tested = 0
    for counts in product(range(3), repeat=8):
        rows = tuple(row for row, count in enumerate(counts) for _ in range(count))
        for b in (1, 2):
            for axis in range(3):
                left = tuple(row for row in rows if not row & (1 << axis))
                right = tuple(row for row in rows if row & (1 << axis))
                check_split(rows, left, right, axis, 3, b)
                tested += 1
    return tested


def check_actual_files():
    rng = Random(14159265)
    count = internal = private_rows = 0
    for n in (6, 7, 8):
        masks = [sum(1 << i for i in t) for t in combinations(range(n), 3)]
        for _ in range(70):
            formula = [(s, rng.getrandbits(n) & s) for s in masks]
            failed = [[j for j, (s, p) in enumerate(formula) if row & s == p]
                      for row in range(1 << n)]
            if any(not failures for failures in failed):
                continue
            count += 1
            witnesses = {bad[0]: row for row, bad in enumerate(failed) if len(bad) == 1}
            private_rows += len(witnesses)
            for copies in (1, 2):
                rows = tuple(w for w in witnesses.values() for _ in range(copies))
                root = surviving_supports(rows, n, copies)
                assert all(s.bit_count() < 3 for s in root)
                pending = [rows]
                leaves = 0
                while pending:
                    block = pending.pop()
                    if len(block) <= 4*copies:
                        leaves += 1
                        continue
                    for axis in range(n):
                        left = tuple(w for w in block if not w & (1 << axis))
                        right = tuple(w for w in block if w & (1 << axis))
                        if min(len(left), len(right)) > copies:
                            check_split(block, left, right, axis, n, copies)
                            pending.extend([left, right])
                            internal += 1
                            break
                    else:
                        raise AssertionError("large block failed to split")
                assert leaves <= max(1, len(root))
    assert internal and count and private_rows
    return count, internal, private_rows


def main():
    assert EDGES[0] == 7 and EDGES[-1] == SIX ^ 7
    splits = weighted_checks()
    count_files, nodes, private_rows = check_actual_files()
    print(f"{splits:,} weighted support splits; {count_files} exhaustive UNSAT files, "
          f"{private_rows} private rows, {nodes} nontrivial witness splits")
    options = tuple(blocker_options(e) for e in EDGES)
    best = 0
    extrema = []
    # Other than two specified complementary edges, 18 independent edge choices.
    # Omit the graph containing all 20 edges.
    count = (1 << 18) - 1
    for middle in range(count):
        family = (1 << 19) | (middle << 1) | 1
        weight = sum(scaled_weight(block) for _, block in best_blockers(family, options))
        if weight > best:
            best = weight
            extrema = []
        if weight == best:
            extrema.append(family)
    assert best == 57 and len(extrema) == 18
    for family in extrema:
        check_worst_by_permutations(family, options)
    check_cube_mass()
    print(f"{check_small_forests():,} admissible labeled 6-by-6 mixed-line graphs; maximum 10 edges")
    check_grid()
    assert 2**37 > 20 * comb(43, 6) * (1 + 43 + comb(43, 2))
    assert 2**36 <= 20 * comb(42, 6) * (1 + 42 + comb(42, 2))
    print(f"{count:,} proper families, {len(extrema)} maximizers, maximum {best}/60")
    print("684 of 720 permutations covered for each maximizer; 43-variable threshold verified")


if __name__ == "__main__":
    main()
