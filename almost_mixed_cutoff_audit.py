"""Test the degree-four cutoff reduction on all subsets of the eight three-variable clauses."""

from collections import Counter, defaultdict
from itertools import product

import pycosat

from one_byte_dense_successor_audit import clause, encode, parse


def clause_copies(source, fresh):
    occurrences = defaultdict(list)
    entries = []
    for row in source:
        literals = []
        for lit in row:
            copy = fresh()
            occurrences[abs(lit)].append(copy)
            literals.append(copy if lit > 0 else -copy)
        entries.append(literals)
    links = []
    for copies in occurrences.values():
        if len(copies) >= 2:
            links.extend(zip(copies, copies[1:] + copies[:1]))

    return entries, links


def make_formula(source, pair_test=False):
    next_name = 0

    def fresh():
        nonlocal next_name
        next_name += 1
        return next_name

    high, low, helper = fresh(), fresh(), fresh()
    first_root_literal = -high if pair_test else high
    rows = [(first_root_literal, low, helper), (first_root_literal, low, -helper)]
    entries, links = clause_copies(source, fresh)
    rails = [(fresh(), fresh()) for _ in range(len(entries) + len(links))]
    left, right = high, low
    for f, t in rails:
        rows.extend(((left, -right, -f), (left, -right, t)))
        left, right = f, t

    for (a, b, c), (f, t) in zip(entries, rails):
        u, v = fresh(), fresh()
        rows.extend(((f, a, -u), (u, b, -v), (v, c, -t)))
    for (a, b), (f, _) in zip(links, rails[len(entries):]):
        rows.append((-a, b, f))

    ordering = list(range(3, next_name + 1)) + [low, high]
    names = {old: new for new, old in enumerate(ordering, start=1)}
    def rename(lit):
        return names[abs(lit)] if lit > 0 else -names[abs(lit)]
    physical = {clause(*(rename(lit) for lit in row)) for row in rows}
    assert len(rows) == len(physical)
    assert names[high] == next_name and names[low] == next_name - 1
    return encode(physical), names[high], names[low]


def two_exception_formula(source, regular=False, *, prefix_delay=0):
    if prefix_delay < 0:
        raise ValueError("prefix_delay must be nonnegative")
    next_name = 0

    def fresh():
        nonlocal next_name
        next_name += 1
        return next_name

    roots = [fresh() for _ in range(3)]
    rows = [tuple(roots), tuple(-x for x in roots)]
    positives, negatives = [], []
    for root in roots:
        a, b, c, d = (fresh() for _ in range(4))
        rows.extend(((-root, a, b), (root, -c, -d)))
        positives.extend((a, b))
        negatives.extend((c, d))
    entries, links = clause_copies(source, fresh)

    def chain(root, trigger, count):
        if not (count or prefix_delay):
            return []
        first, guard = fresh(), fresh()
        rows.extend(((-trigger * root, trigger * first, guard),
                     (-trigger * root, trigger * first, -guard)))
        values = [root, first]
        for _ in range(prefix_delay + count):
            new = fresh()
            rows.append((-trigger * values[-2], -trigger * values[-1], trigger * new))
            values.append(new)
        return values[2 + prefix_delay:]

    true_banks = [iter(chain(q, 1, 4 * len(entries))) for q in positives]
    false_banks = [iter(chain(p, -1, 4 * (len(entries) + len(links)))) for p in negatives]

    def forced_pad(banks, value):
        pad = fresh()
        for start in (0, 3):
            first, second = fresh(), fresh()
            for node in (first, second):
                for bank in banks[start:start + 3]:
                    a, b = next(bank), next(bank)
                    rows.append((-value * a, -value * b, value * node))
            rows.append((-value * first, -value * second, value * pad))
        return pad

    for a, b, c in entries:
        f, t = forced_pad(false_banks, -1), forced_pad(true_banks, 1)
        u, v = fresh(), fresh()
        rows.extend(((f, a, -u), (u, b, -v), (v, c, -t)))
    for a, b in links:
        rows.append((-a, b, forced_pad(false_banks, -1)))
    assert all(next(bank, None) is None for bank in true_banks + false_banks)
    if regular:
        degrees = Counter(abs(lit) for row in rows for lit in row)
        for x, degree in sorted(degrees.items()):
            for _ in range(4 - degree):
                a, b, c, d, e = (fresh() for _ in range(5))
                aux = (a, b, c, d, e)
                rows.append((x, a, -b))
                for left, right in ((a, c), (c, b), (b, d), (d, e), (e, a), (a, b)):
                    first, second, third = [v for v in aux if v not in (left, right)]
                    rows.append((first, -second, third))
    physical = {clause(*row) for row in rows}
    assert len(physical) == len(rows)
    return encode(physical)


def checked_solve(rows, units):
    queried = [*rows, *((x,) for x in units)]
    result = pycosat.solve(queried)
    if result == 'UNSAT':
        return False
    assert isinstance(result, list)
    true_literals = set(result)
    assert all(-x not in true_literals for x in true_literals)
    assert all(any(x in true_literals for x in row) for row in queried)
    return True


def uniform_subcube(rows, variable_count):
    # (False, j) denotes flipping j away from all-zero; True denotes the dual.
    vertices = {(center, j) for center in (False, True)
                for j in range(1, variable_count + 1)}
    edges = []
    for row in rows:
        positive = [x for x in row if x > 0]
        negative = [-x for x in row if x < 0]
        for center, at_center in ((False, negative), (True, positive)):
            if len(at_center) == 1:
                vertices.discard((center, at_center[0]))
            else:
                a, b = at_center
                edges.append(((center, a), (center, b)))
    adjacency = {x: set() for x in vertices}
    for a, b in edges:
        if a in vertices and b in vertices:
            adjacency[a].add(b)
            adjacency[b].add(a)
    high = {x for x in vertices if len(adjacency[x]) == 4}
    isolated = {(not c, j) for c, j in high}
    assert len(isolated) == len(high) and all(not adjacency[x] for x in isolated)
    remaining = vertices - high - isolated
    colors = {}
    for x in sorted(remaining):
        used = {colors[y] for y in adjacency[x] if y in colors}
        colors[x] = next(c for c in range(4) if c not in used)
    best = max(range(4), key=lambda c: sum(value == c for value in colors.values()))
    independent = isolated | {x for x, c in colors.items() if c == best}
    center = max((False, True), key=lambda b: sum(c == b for c, _ in independent))
    free = {j for c, j in independent if c == center}
    assert 12 * len(free) >= variable_count
    # Each row has a fixed literal true on the entire returned face.
    assert all(any((x > 0) == center and abs(x) not in free for x in row) for row in rows)
    return len(free)


def sharp_cube_gadget():
    y = (1, 2, 3, 4)
    z = (5, 6, 7, 8)
    w = (9, 10, 11, 12)

    def rows(x):
        a, b, c, d = x
        u, v, s, t = w
        return [(-a, -b, c), (-a, -c, d), (-a, -d, b), (-b, -c, a),
                (-b, -d, u), (-c, -d, v), (-u, -s, t), (-v, -t, s)]
    gadget = rows(y) + [tuple(-lit for lit in row) for row in rows(z)]
    raw = encode({clause(*row) for row in gadget})
    body = parse(raw)
    assert Counter(abs(x) for row in body for x in row) == {i: 4 for i in range(1, 13)}
    sizes = []
    for center in (False, True):
        best = 0
        for mask in range(1 << 12):
            if all(any((lit > 0) == center and not mask & (1 << (abs(lit) - 1))
                       for lit in row) for row in body):
                best = max(best, mask.bit_count())
        sizes.append(best)
    assert sizes == [1, 1] and uniform_subcube(body, 12) == 1
    return len(raw)


def signed_catalog():
    return [tuple(i if not mask & (1 << (i - 1)) else -i for i in (1, 2, 3))
            for mask in range(8)]


def source_has_model(source):
    return any(all(any(values[abs(lit) - 1] == (lit > 0) for lit in row) for row in source)
               for values in product((False, True), repeat=3))


def main():
    catalog = signed_catalog()
    mixed_depths = Counter()
    max_bytes = 0
    greatest_degree = 0
    largest_two_exception = 0
    smallest_mutants = None
    largest_face = 0
    largest_body_face = 0
    projections = 0
    largest_regular = 0
    regular_projections = 0
    for chosen in range(256):
        source = [row for i, row in enumerate(catalog) if chosen & (1 << i)]
        truth = source_has_model(source)
        raw, high, low = make_formula(source)
        rows = parse(raw)
        counts = Counter(abs(lit) for row in rows for lit in row)
        assert max(counts.values()) <= 4
        assert sum(all(x > 0 for x in row) for row in rows) == 1
        assert all(any(x > 0 for x in row) for row in rows)
        assert all(any(x > 0 and x != low or x == -low for x in row) for row in rows)

        # Exclusive cutoffs on the all-zero path impose successive high bits zero.
        below_all = checked_solve(rows, [])
        below_half = checked_solve(rows, [-high])
        below_quarter = checked_solve(rows, [-high, -low])
        assert below_all and below_half == truth and not below_quarter
        depths = [d for d, (before, after) in enumerate(
            ((below_all, below_half), (below_half, below_quarter)), start=1)
            if before != after]
        assert depths == [2 if truth else 1]
        mixed_depths[depths[0]] += 1
        other = two_exception_formula(source)
        doubly_mixed = parse(other)
        loads = Counter(abs(lit) for row in doubly_mixed for lit in row)
        assert max(loads.values()) <= 4
        assert sum(all(x > 0 for x in row) for row in doubly_mixed) == 1
        assert sum(all(x < 0 for x in row) for row in doubly_mixed) == 1
        pure_positive = next(row for row in doubly_mixed if min(row) > 0)
        pure_negative = next(row for row in doubly_mixed if max(row) < 0)
        assert pure_positive == tuple(-x for x in pure_negative)
        assert checked_solve(doubly_mixed, []) == truth
        body = doubly_mixed - {pure_positive, pure_negative}
        largest_body_face = max(largest_body_face, uniform_subcube(body, len(loads)))
        for setting in product((False, True), repeat=3):
            units = [x if bit else -x for x, bit in zip(pure_positive, setting)]
            assert checked_solve(body, units) == (len(set(setting)) == 1 or truth)
            projections += 1

        regular_raw = two_exception_formula(source, regular=True)
        regular_rows = parse(regular_raw)
        regular_degrees = Counter(abs(lit) for row in regular_rows for lit in row)
        assert set(regular_degrees.values()) == {4}
        assert [row for row in regular_rows if min(row) > 0] == [pure_positive]
        assert [row for row in regular_rows if max(row) < 0] == [pure_negative]
        assert checked_solve(regular_rows, []) == truth
        regular_body = regular_rows - {pure_positive, pure_negative}
        for setting in product((False, True), repeat=3):
            units = [x if bit else -x for x, bit in zip(pure_positive, setting)]
            assert checked_solve(regular_body, units) == (len(set(setting)) == 1 or truth)
            regular_projections += 1
        largest_regular = max(largest_regular, len(regular_raw))

        pair_raw, h, l = make_formula(source, pair_test=True)
        pair_rows = parse(pair_raw)
        assert all(min(row) < 0 < max(row) for row in pair_rows)
        pair_degrees = Counter(abs(x) for row in pair_rows for x in row)
        assert max(pair_degrees.values()) <= 4
        assert not checked_solve(pair_rows, [h, -l])
        assert checked_solve(pair_rows, [-h, l]) == truth
        # A mixed row excludes one of the two constant vectors' single-bit neighbors.
        forbidden = set()
        for row in pair_rows:
            minority_positive = sum(x > 0 for x in row) == 1
            (only,) = [x for x in row if (x > 0) == minority_positive]
            forbidden.add(only)
        largest_face = max(largest_face, uniform_subcube(pair_rows, len(pair_degrees)))
        mutants = 2 * len(pair_degrees) - len(forbidden)
        assert 3 * mutants >= 2 * len(pair_degrees)
        smallest_mutants = mutants if smallest_mutants is None else min(smallest_mutants, mutants)
        largest_two_exception = max(largest_two_exception, len(other))
        max_bytes = max(max_bytes, len(raw))
        greatest_degree = max(greatest_degree, max(counts.values()))

    assert mixed_depths == {1: 1, 2: 255} and greatest_degree == 4
    size = sharp_cube_gadget()
    print(f'12-variable sharp gadget: 8,192 centered cubes checked, maximum dimension 1; {size} bytes')
    print(f'256 canonical sources; unique mixed depth 1 on {mixed_depths[1]}, '
          f'depth 2 on {mixed_depths[2]}; maximum occurrence {greatest_degree}; '
          f'largest generated file {max_bytes} bytes')
    print(f'256 formulas with one exceptional NAE triple; '
          f'largest generated file {largest_two_exception} bytes; {projections} root projections; '
          f'largest certified body face dimension {largest_body_face}')
    print(f'256 exactly four-regular files; {regular_projections} projections; '
          f'largest generated file {largest_regular} bytes')
    print(f'256 all-mixed pair-equivalence tests; minimum one-bit models {smallest_mutants}; '
          f'largest certified face dimension {largest_face}')


if __name__ == '__main__':
    main()
