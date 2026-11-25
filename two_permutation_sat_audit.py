"""Check the positive one-in-three compiler using an independent exact-cover count."""

from collections import defaultdict
from functools import lru_cache
from itertools import product
from random import Random


def compile_source(source):
    triples = [row[t:] + row[:t] for row in source for t in range(3)]
    occurrences = [name for row in triples for name in row]
    by_name = defaultdict(lambda: [[], [], []])
    for i, name in enumerate(occurrences):
        by_name[name][i % 3].append(i)
    next_id = {}
    for slots in by_name.values():
        assert len(slots[0]) == len(slots[1]) == len(slots[2])
        cycle = [i for block in zip(*slots) for i in block]
        for i, j in zip(cycle, cycle[1:] + cycle[:1]):
            assert j % 3 == (i+1) % 3 and i != j
            next_id[i] = j

    # A row is initially a tuple of (wire, color) incidences.
    colored = []
    for j in range(len(triples)):
        for tag, offset in [('x', 0), ('w', 0), ('w', 1)]:
            colored.append([((tag, 3*j+s), (s+offset) % 3) for s in range(3)])
    for i in range(len(occurrences)):
        for tag, j, color in [('x', i, i+1), ('x', next_id[i], i), ('w', i, i+2)]:
            colored.append([((tag, j), color % 3),
                            (('a', i), (color+1) % 3), (('b', i), (color+2) % 3)])

    order = []
    incident_colors = defaultdict(list)
    for row in colored:
        assert {c for _, c in row} == {0, 1, 2} and len({wire for wire, _ in row}) == 3
        sorted_row = tuple(wire for wire, _ in sorted(row, key=lambda item: item[1]))
        order.append(sorted_row)
        for wire, color in row:
            incident_colors[wire].append(color)
    assert all(sorted(cs) == [0, 1, 2] for cs in incident_colors.values())
    label = {row[0]: j for j, row in enumerate(order)}
    assert len(label) == len(order) == len(incident_colors) == 12*len(triples)
    assert label.keys() == incident_colors.keys()
    p = tuple(label[row[1]] for row in order)
    q = tuple(label[row[2]] for row in order)
    labels = list(range(len(order)))
    assert sorted(p) == sorted(q) == labels
    assert all(len({j, p[j], q[j]}) == 3 for j in labels)
    return p, q, label, occurrences


def cover_count(p, q, fixed):
    """Algorithm X on just the two permutations and requested 0/1 pins.

    Selecting a label covers all rows containing it. Distinct labels that
    cover identical rows remain distinct candidate choices in the recurrence.
    """
    rows = [(i, a, b) for i, (a, b) in enumerate(zip(p, q))]
    covers = [0] * len(rows)
    for i, row in enumerate(rows):
        for label in row:
            covers[label] |= 1 << i
    untouched = (1 << len(rows))-1
    selected = set()
    for label, value in fixed.items():
        if value:
            cover = covers[label]
            if cover & untouched != cover:
                return 0, None
            untouched ^= cover
            selected.add(label)
    choices = [[v for v in row if fixed.get(v, True)] for row in rows]

    def branch(mask):
        smallest = None
        pending = mask
        while pending:
            bit = pending & -pending
            row = choices[bit.bit_length()-1]
            available = tuple(v for v in row if covers[v] & mask == covers[v])
            if not available:
                return ()
            if smallest is None or len(available) < len(smallest):
                smallest = available
            pending ^= bit
        return smallest

    @lru_cache(None)
    def count(mask):
        if not mask:
            return 1
        return sum(count(mask ^ covers[v]) for v in branch(mask))

    total = count(untouched)
    if not total:
        return 0, None
    while untouched:
        value = next(v for v in branch(untouched) if count(untouched ^ covers[v]))
        selected.add(value)
        untouched ^= covers[value]
    return total, selected


def satisfies(source, assignment):
    return all(sum(assignment[v] for v in row) == 1 for row in source)


def encode(occurrences, label, assignment, switch):
    selected = set()
    for i, v in enumerate(occurrences):
        if assignment[v]:
            selected.update((label['x', i], label['w', i]))
        elif switch(i):
            selected.add(label['a', i])
        else:
            selected.add(label['b', i])
    return selected


def verify_and_decode(p, q, label, occurrences, selected):
    assert all(sum(v in selected for v in (j, p[j], q[j])) == 1 for j in range(len(p)))
    # Using the inverse permutations turns the preimages into images.
    sets = [set(selected), {j for j in range(len(p)) if p[j] in selected},
            {j for j in range(len(q)) if q[j] in selected}]
    inverse_p = {value: i for i, value in enumerate(p)}
    inverse_q = {value: i for i, value in enumerate(q)}
    assert sets[1] == {inverse_p[v] for v in selected}
    assert sets[2] == {inverse_q[v] for v in selected}
    assert set.union(*sets) == set(range(len(p))) and sum(map(len, sets)) == len(p)
    result = {}
    for i, v in enumerate(occurrences):
        bit = label['x', i] in selected
        assert bit == (label['w', i] in selected) == result.setdefault(v, bit)
        assert sum(label[tag, i] in selected for tag in ('a', 'b')) == 1-bit
    return result


def audit_source(source):
    p, q, label, occurrences = compile_source(source)
    names = sorted(set(occurrences))
    representatives = {v: label['x', occurrences.index(v)] for v in names}
    all_count, first = cover_count(p, q, {})
    if first is not None:
        assert satisfies(source, verify_and_decode(p, q, label, occurrences, first))
    factor = 1 << (2 * (3*len(source)))
    valid = witnesses = 0
    for values in product((0, 1), repeat=len(names)):
        assignment = dict(zip(names, values))
        fixed = {representatives[v]: bit for v, bit in assignment.items()}
        count, witness = cover_count(p, q, fixed)
        if not satisfies(source, assignment):
            assert count == 0 and witness is None
            continue
        assert count == factor
        assert verify_and_decode(p, q, label, occurrences, witness) == assignment
        valid += 1
        for switch in [lambda i: False, lambda i: True, lambda i: i % 2 == 0]:
            explicit = encode(occurrences, label, assignment, switch)
            assert verify_and_decode(p, q, label, occurrences, explicit) == assignment
            witnesses += 1
    assert all_count == valid * factor
    return 1 << len(names), valid, all_count, witnesses


if __name__ == '__main__':
    rows = list(product(range(3), repeat=3))
    suite = [()] + [(row,) for row in rows] + list(product(rows, repeat=2))
    rng = Random(2309)
    for length in (3, 4):
        for _ in range(12):
            suite.append(tuple(tuple(rng.randrange(5) for _ in range(3)) for _ in range(length)))
    totals = tuple(map(sum, zip(*(audit_source(source) for source in suite))))
    print('source formulas:', len(suite), '(757 exhaustive, 24 seeded)')
    print('source assignments, satisfying assignments, exact covers counted, constructed witnesses:',
          *totals)
