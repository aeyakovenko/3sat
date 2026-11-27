"""Check least-witness pruning on arbitrary colors and on physical DIMACS switches."""

import argparse
from collections import Counter
from functools import partial
from itertools import combinations, product

import pycosat

from one_byte_dense_successor_audit import clause, encode, parse
from selector_parity_cube_audit import Names, physical_template


def cutoff_logic(cutoffs, copies, variable_count, source, _unused, arity):
    assert arity == copies * len(cutoffs)
    ids = Names()
    variables = [ids.new() for _ in range(variable_count)]
    switches = [ids.new() for _ in range(arity)]
    false_bit, pad1, pad2 = (ids.new() for _ in range(3))
    rows = list(source)
    for a, b in product((1, -1), repeat=2):
        rows.append((-false_bit, a * pad1, b * pad2))
    for index, cutoff in enumerate(cutoffs):
        # For an empty low-order prefix, its integer value is always <= zero.
        previous = -false_bit
        for position, bit in enumerate(variables):
            out = ids.new()
            left = -bit
            right = previous
            if cutoff & (1 << position):
                gates = [(out, -left), (out, -right), (-out, left, right)]
            else:
                gates = [(-out, left), (-out, right), (out, -left, -right)]
            # The two initial constants can produce a tautology or repetition.
            for row in gates:
                simplified = set(row)
                if -false_bit in simplified or any(-x in simplified for x in simplified):
                    continue
                simplified.discard(false_bit)
                ordered = sorted(simplified, key=abs)
                if len(ordered) == 1:
                    for a, b in product((1, -1), repeat=2):
                        rows.append((ordered[0], a * pad1, b * pad2))
                elif len(ordered) == 2:
                    rows.append((*ordered, false_bit))
                else:
                    assert len(ordered) == 3
                    rows.append(tuple(ordered))
            previous = out
        for bit in switches[index * copies:(index + 1) * copies]:
            rows.append((-bit, previous, false_bit))
    return rows, switches


def check_row(width, group_count, multiplicity):
    # Every assignment of two colors to every copy, including ties.
    copies = 2 * (multiplicity - 1) + 1
    checked = 0
    for assignment in product(range(2), repeat=group_count * copies):
        groups = [assignment[pos:pos + copies] for pos in range(0, len(assignment), copies)]
        heavy = [min(set(row), key=lambda x: (-row.count(x), x)) for row in groups]
        first_index = {}
        for j, color in enumerate(heavy):
            first_index.setdefault(color, j)
        kept = set(first_index.values())
        assert len(kept) <= 2
        for endpoints in combinations(range(1 << width), group_count):
            for least in range(1 << width):
                containing = next((j for j, end in enumerate(endpoints) if least <= end), None)
                if containing is None or containing in kept:
                    continue
                j = containing
                i = first_index[heavy[j]]
                assert endpoints[i] < least <= endpoints[j]
                assert all(groups[t].count(heavy[j]) >= multiplicity for t in (i, j))
                checked += 1
    return checked


def source_fixture():
    variable_count = 3
    satisfying = {5, 6}
    source = [
        tuple(-i if number & (1 << (i - 1)) else i for i in range(1, variable_count + 1))
        for number in range(1 << variable_count) if number not in satisfying
    ]
    return variable_count, satisfying, source


def physical_host(source, v, cutoffs, copies):
    arity = copies * len(cutoffs)
    fixed, selectors, variable_count = physical_template(
        source, [], arity, h=4,
        semantic_builder=partial(cutoff_logic, cutoffs, copies, v),
    )
    base = encode(fixed | {clause(p, q, a) for p, q, a, _ in selectors})
    return fixed, selectors, variable_count, base


def physical_fixture():
    v, satisfying, source = source_fixture()
    cutoffs = [0, 4, 5, 6, 7]
    copies = 3
    arity = copies * len(cutoffs)
    fixed, selectors, variable_count, base = physical_host(source, v, cutoffs, copies)
    verdicts, coordinates, files = [], [], []
    for selected, (p, q, a, b) in enumerate(selectors):
        marker = f'\n{p} {q} {a} 0'.encode()
        assert base.count(marker) == 1
        position = base.index(marker) + len(marker) - 3
        assert base[position] == ord('2') and str(b)[:-1] == str(a)[:-1]
        new = bytearray(base)
        new[position] ^= 1
        raw = bytes(new)
        rows = parse(raw)
        assert encode(rows) == raw
        degrees = Counter(abs(literal) for row in rows for literal in row)
        assert set(degrees) == set(range(1, variable_count + 1)) and max(degrees.values()) <= 4
        truth = any(model <= cutoffs[selected // copies] for model in satisfying)
        answer = pycosat.solve(list(rows))
        if truth:
            assert isinstance(answer, list)
            model = set(answer)
            assert all(-x not in model for x in model)
            assert all(any(literal in model for literal in row) for row in rows)
        else:
            assert answer == 'UNSAT'
        coordinates.append(position)
        files.append(raw)
        verdicts.append(truth)
    expected_histogram = Counter(files[0])
    assert len(set(coordinates)) == arity
    assert all(Counter(raw) == expected_histogram for raw in files)
    assert all(sum((a ^ b).bit_count() for a, b in zip(files[i], files[j])) == 2
               for i, j in combinations(range(arity), 2))
    # A single native read-only statistic on the serialized bytes with two replies.
    buckets = {}
    for raw, truth in zip(files, verdicts):
        reply = sum(byte.bit_count() for byte in raw[::2]) % 2
        buckets.setdefault(reply, Counter())[truth] += 1
    mixed = max(min(count[False], count[True]) for count in buckets.values())
    assert mixed >= 2
    return len(base), variable_count, len(fixed) + arity, arity, mixed


def native_observation(raw):
    # Five stored instructions: LOAD from 0; AND with 1023; indirect LOAD;
    # AND with 1; branch to YES if nonzero, otherwise NO.
    byte_width = 2 * (((8 * len(raw) + 1).bit_length() + 15) // 16)
    def load(address):
        start = address * byte_width
        return int.from_bytes(raw[start:start + byte_width], 'little')
    address = load(0) & 1023
    return (load(address) & 1) != 0, (0, address)


def search_with_observer(v, source, satisfying):
    prefixes = [0]
    copies = 4  # K=3 possible timed replies, desired multiplicity r=2.
    first_mixed = None
    trials = 0
    for depth in range(1, v + 1):
        children = [2 * prefix + bit for prefix in prefixes for bit in (0, 1)]
        cutoffs = [((child + 1) << (v - depth)) - 1 for child in children]
        _, selectors, _, center = physical_host(source, v, cutoffs, copies)
        colors = []
        for p, q, a, _ in selectors:
            marker = f'\n{p} {q} {a} 0'.encode()
            assert center.count(marker) == 1
            pos = center.index(marker) + len(marker) - 3
            raw = bytearray(center)
            raw[pos] ^= 1
            color, trace = native_observation(raw)
            assert trace[1] != 0 and 5 < 8 * len(raw)
            colors.append(color)
            trials += 1
        retained = {}
        for j, child in enumerate(children):
            bucket = colors[j * copies:(j + 1) * copies]
            color = min(set(bucket), key=lambda x: (-bucket.count(x), x))
            assert bucket.count(color) >= 2
            if color not in retained:
                retained[color] = j
            elif satisfying and child == min(satisfying) >> (v - depth) and first_mixed is None:
                i = retained[color]
                assert cutoffs[i] < min(satisfying) <= cutoffs[j]
                first_mixed = (depth, cutoffs[i], cutoffs[j], color)
        prefixes = [children[j] for j in sorted(retained.values())]
    accepted = any(w in satisfying for w in prefixes)
    if satisfying and not accepted:
        assert first_mixed is not None
    return accepted, trials, first_mixed


def check_failed_search():
    v, satisfying, source = source_fixture()
    assert all(any(bool(5 & (1 << (abs(lit) - 1))) == (lit > 0)
                   for lit in row) for row in source)
    accepted, trials, first_mixed = search_with_observer(v, source, satisfying)
    assert not accepted
    print(f'{trials} timed indirect-read runs; source witness 5; first lost cutoff pair {first_mixed}')


def check_catalog():
    # In the empty core there are no occurring variables after normalization.
    # It is accepted immediately with the empty assignment.
    clauses = [tuple(-j if a & (1 << (j - 1)) else j for j in range(1, 4))
               for a in range(8)]
    checked, failed, trials = 1, 0, 0
    for chosen in range(1, 256):
        source = [row for i, row in enumerate(clauses) if chosen & (1 << i)]
        satisfying = {a for a in range(8)
                      if all(any(bool(a & (1 << (abs(z) - 1))) == (z > 0)
                                 for z in row) for row in source)}
        accepted, runs, _ = search_with_observer(3, source, satisfying)
        checked += 1
        trials += runs
        failed += bool(satisfying) and not accepted
        assert accepted == (0 in satisfying)
        if chosen == 1:
            assert source == [(1, 2, 3)] and not accepted and min(satisfying) == 1
    assert (checked, failed) == (256, 127)
    print(f'{checked} three-variable clause subsets, {trials} actual observer runs, {failed} false negatives')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full-three-variable', action='store_true', help='try every subset of the eight clause signs')
    args = parser.parse_args()
    losses = check_row(3, 3, 2) + check_row(3, 4, 1)
    print(f'{losses} verified losses of a least witness across exhaustive colorings and cutoffs')
    size, names, rows, count, mixed = physical_fixture()
    print(f'{count} one-hot files of {size} bytes, {names} variables, {rows} clauses')
    print(f'one alternating-byte parity bucket contains at least {mixed} files of each SAT verdict')
    check_failed_search()
    if args.full_three_variable:
        check_catalog()
