"""Exact two-state model counting and finite tests of the fixed three-state readers."""

from itertools import product
from random import Random

from fixed_routing_sat_audit import Controls, accepts_left, switch_count


def step(table, b, state):
    return (table >> (2 * b + state)) & 1


def count_two_state(rows, variables, start=0, target=1):
    """Tally powers of two in disjoint last-reset cases, then propagate carries."""
    # A factor lists the contributions of the two variable values to suffix parity.
    # None excludes that value because it would reset somewhere in the suffix.
    factors = [(0, 0)] * variables
    empty = flexible = base = 0
    free = variables
    histogram = [0] * (variables + 2)

    def update(name, new):
        nonlocal empty, flexible, free, base
        for pair, change in ((factors[name], -1), (new, 1)):
            a, b = pair
            empty += change * (a is None and b is None)
            if a is not None and b is not None:
                free += change
                flexible += change * (a != b)
            base ^= a if a is not None else (b or 0)
        factors[name] = new

    def record(state):
        if not empty and (flexible or (state ^ base) == target):
            histogram[free - bool(flexible)] += 1

    for name, table in reversed(rows):
        old = factors[name]
        keep = [None, None]
        for b in range(2):
            if old[b] is None:
                continue
            lo, hi = step(table, b, 0), step(table, b, 1)
            if lo == hi:
                pinned = [None, None]
                pinned[b] = old[b]
                update(name, tuple(pinned))
                record(lo)
                update(name, old)
            else:
                keep[b] = old[b] ^ lo
        update(name, tuple(keep))
    record(start)
    for i in range(variables + 1):
        carry, histogram[i] = divmod(histogram[i], 2)
        histogram[i + 1] += carry
    assert not histogram[-1]
    # Packing to a Python integer here is for comparison with brute force.
    return sum(bit << i for i, bit in enumerate(histogram))


def brute_count(rows, variables, start, target):
    hits = 0
    for x in range(1 << variables):
        state = start
        for name, table in rows:
            state = step(table, x >> name & 1, state)
        hits += state == target
    return hits


def network_trace(left, controls):
    """Give every switch its two fresh output wire names; order is input-independent."""
    values = list(left)
    switches = []

    def stage(lanes, offset):
        half = len(lanes) // 2
        first, second = [], []
        for i, (a, b) in enumerate(zip(lanes[:half], lanes[half:])):
            p = len(values)
            bit = controls[offset + i]
            values.extend((values[b], values[a]) if bit else (values[a], values[b]))
            switches.append((a, b, p, p + 1, bit))
            first.append(p)
            second.append(p + 1)
        return first, second

    def trace(lanes, offset):
        first, second = stage(lanes, offset)
        if len(lanes) == 2:
            return first + second
        half = len(first)
        inner = switch_count(half)
        mid = trace(first, offset + half) + trace(second, offset + half + inner)
        top, bottom = stage(mid, offset + half + 2 * inner)
        return top + bottom

    right = trace(list(range(len(left))), 0)
    return switches, right, values


def compile_readers(left, control):
    switches, right, values = network_trace(left, control.settings)
    clauses = []

    def eq(a, b, enabled):
        clauses.extend([(enabled, ((a, 1), (b, 0))), (enabled, ((a, 0), (b, 1)))])

    for i, enabled in enumerate(control.joined):
        eq(i, i + 1, enabled)
    for a, b, p, q, cross in switches:
        for u, v, enabled in ((a, p, not cross), (b, q, not cross),
                              (a, q, cross), (b, p, cross)):
            eq(u, v, enabled)
    for j, enabled in enumerate(control.enabled):
        pin = control.pins[j]
        clauses.append((pin is not None, ((right[4 * j], int(pin == 0)),)))
        clauses.append((enabled, tuple((right[4 * j + i + 1], control.negative[3 * j + i])
                                       for i in range(3))))
    occurrences = [wire for _, clause in clauses for wire, _ in clause]
    groups = [[] for _ in values]
    for i, wire in enumerate(occurrences):
        groups[wire].append(i)
    assert all(groups)
    word = [values[wire] for wire in occurrences]
    return clauses, groups, word


def accepts_rows(clauses, word):
    # 0 = no true literal yet, 1 = some true literal, 2 = rejecting sink.
    state = offset = 0
    for enabled, clause in clauses:
        for j, (_, negated) in enumerate(clause):
            bit = word[offset]
            offset += 1
            if state == 2:
                continue
            state = int(state == 1 or bit != negated or not enabled)
            if j + 1 == len(clause):
                state = 0 if state else 2
    return state == 0


def accepts_groups(groups, word):
    state = 0
    for group in groups:
        for j, i in enumerate(group):
            if state == 2:
                continue
            if j == 0:
                state = word[i]
            elif state != word[i]:
                state = 2
    return state != 2


def check_two():
    cases = 0
    for names in product(range(2), repeat=3):
        for tables in product(range(16), repeat=3):
            rows = list(zip(names, tables))
            for start, target in product(range(2), repeat=2):
                assert count_two_state(rows, 2, start, target) == brute_count(rows, 2, start, target)
                cases += 1
    rng = Random(319)
    for _ in range(400):
        v = rng.randrange(1, 9)
        rows = [(rng.randrange(v), rng.randrange(16)) for _ in range(rng.randrange(26))]
        start, target = rng.randrange(2), rng.randrange(2)
        assert count_two_state(rows, v, start, target) == brute_count(rows, v, start, target)
    print(f"{cases} exhaustive and 400 additional two-state model counts")


def check_three():
    rng = Random(2611)
    cases = changed = corrupt = 0
    for r, trials in ((4, 128), (8, 12)):
        shape = None
        for _ in range(trials):
            bits = lambda n: tuple(rng.randrange(2) for _ in range(n))
            c = Controls(bits(switch_count(r)), bits(r - 1), bits(3 * r // 4), bits(r // 4),
                         tuple(rng.choice((None, 0, 1)) for _ in range(r // 4)))
            for left in product(range(2), repeat=r):
                clauses, groups, word = compile_readers(left, c)
                if shape is None:
                    shape = groups
                assert groups == shape
                assert accepts_groups(groups, word)
                assert accepts_rows(clauses, word) == accepts_left(left, c)
                cases += 1
            # Changing a whole internal wire keeps the second reader happy,
            # but its defining switch must then reject in the first reader.
            for group in groups[r:]:
                bad = list(word)
                for i in group:
                    bad[i] ^= 1
                assert accepts_groups(groups, bad) and not accepts_rows(clauses, bad)
                if len(group) > 1:
                    bad[group[0]] ^= 1
                    assert not accepts_groups(groups, bad)
                corrupt += 1
            # Try inconsistent witnesses without deriving their bits from wires.
            for _ in range(8):
                test = bits(len(word))
                assert accepts_groups(groups, test) == all(
                    len({test[i] for i in group}) == 1 for group in groups)
                changed += 1
    print(f"{cases} circuit-trace valuations, {corrupt} corrupted internal wires, {changed} independent words")


if __name__ == "__main__":
    check_two()
    check_three()
