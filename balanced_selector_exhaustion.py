"""Exhaust balanced lookup rows and check a packed ordered-selector solver."""

from collections import Counter
from itertools import combinations, permutations, product
from random import Random


def mask_of(values):
    return sum(1 << value for value in values)


def accepted(mask):
    return [v for v in range(8) if mask & (1 << v)]


def majority(a, b, c):
    return (a & b) | (b & c) | (c & a)


NOR = mask_of([x + 2 * y + 4 * int(not (x or y)) for x, y in product(range(2), repeat=2)])


def table_audit():
    gate_orbit = set()
    for ordering in permutations(range(3)):
        permuted = [sum(((v >> source) & 1) << target
                        for target, source in enumerate(ordering)) for v in accepted(NOR)]
        for signs in range(8):
            gate_orbit.add(mask_of(v ^ signs for v in permuted))
    counts = Counter()
    for values in combinations(range(8), 4):
        rows = set(values)
        affine = values[0] ^ values[1] ^ values[2] ^ values[3] == 0
        bijunctive = all(majority(*triple) in rows for triple in combinations(values, 3))
        counts[bijunctive, affine] += 1
        assert (mask_of(rows) in gate_orbit) == (not affine and not bijunctive)
        pair_domains = []
        for i, j in combinations(range(3), 2):
            pair_domains.append((i, j, {((v >> i) & 1, (v >> j) & 1) for v in rows}))
        reconstructed = {v for v in range(8) if all(
            ((v >> i) & 1, (v >> j) & 1) in domain for i, j, domain in pair_domains)}
        assert (reconstructed == rows) == bijunctive
        if bijunctive and not affine:
            assert any(len(domain) == 3 for _, _, domain in pair_domains)
    assert counts == {(True, True): 12, (True, False): 32,
                      (False, True): 2, (False, False): 24}


def packed_decision(rows):
    """Return the verdict and largest boundary, using stable slots for live bits."""
    first, last = {}, {}
    for i, (_, ports) in enumerate(rows):
        for name, _ in ports:
            if name:
                first.setdefault(name, i)
                last[name] = i
    starts = Counter(first.values())
    stops = Counter(last.values())
    live = width = 0
    for i in range(len(rows)):
        live += starts[i] - stops[i]
        width = max(width, live)
    slots = width + 3
    lanes = 1 << slots
    full = (1 << lanes) - 1
    # A run of zeros and then ones repeated across all lanes.
    slot_masks = [full // ((1 << (1 << s)) + 1) << (1 << s) for s in range(slots)]
    possible = full
    assigned = {}
    free = list(range(slots))
    for i, (mask, ports) in enumerate(rows):
        words = []
        names = {name for name, _ in ports if name}
        for name in names:
            if name not in assigned:
                assigned[name] = free.pop()
        for name, sign in ports:
            word = slot_masks[assigned[name]] if name else 0
            words.append(full ^ word if sign else word)
        keep = 0
        for value in accepted(mask):
            term = full
            for j, word in enumerate(words):
                term &= word if value & (1 << j) else full ^ word
            keep |= term
        possible &= keep
        for name in names:
            if last[name] != i:
                continue
            pos = assigned.pop(name)
            delta = 1 << pos
            low = (possible | (possible >> delta)) & (full ^ slot_masks[pos])
            possible = low | (low << delta)
            free.append(pos)
    assert possible in (0, full)
    return bool(possible), width


def exhaustive_decision(rows):
    n = max((name for _, ports in rows for name, _ in ports), default=0)
    for x in range(1 << n):
        good = True
        for mask, ports in rows:
            index = sum(((int(bool(name and x & (1 << (name - 1)))) ^ sign) << j)
                        for j, (name, sign) in enumerate(ports))
            if not mask & (1 << index):
                good = False
                break
        if good:
            return True
    return False


def table_membership(p, table, query):
    false, true = (0, 0), (0, 1)
    rows = []
    nxt = p + 1
    for word in range(1 << p):
        previous = false
        for i in range(p):
            mismatch = (i + 1, (word >> i) & 1)
            # NOR outputs the negation of the running mismatch disjunction.
            rows.append((NOR, (previous, mismatch, (nxt, 0))))
            previous = (nxt, 1)
            nxt += 1
        spare = true if (table >> word) & 1 else false
        rows.append((NOR, (previous, spare, false)))
    for i in range(p):
        mismatch = (i + 1, (query >> i) & 1)
        rows.append((NOR, (mismatch, false, true)))
    return rows


def occurrence_two_rows(clauses):
    """Produce constant-free NOR rows, each name occurring twice."""
    # The test compiler favors clarity over linear-time queue bookkeeping.
    clauses = list(clauses)
    while clauses:
        frequency = Counter(abs(literal) for clause in clauses for literal in clause)
        keep = [clause for clause in clauses if all(frequency[abs(l)] >= 2 for l in clause)]
        if len(keep) == len(clauses):
            break
        clauses = keep

    fresh = 0

    def name():
        nonlocal fresh
        fresh += 1
        return fresh

    def gate(x, y, z):
        return NOR, tuple((abs(l), int(l < 0)) for l in (x, y, z))

    if not clauses:
        return [gate(-1, -2, 3), gate(1, 2, -3)]

    states = {}
    markers = {}
    by_variable = {}
    for i, clause in enumerate(clauses):
        for j, literal in enumerate(clause):
            here = (i, j)
            states[here] = name()
            markers[here] = name()
            by_variable.setdefault(abs(literal), []).append(here)
    successor = {}
    for cycle in by_variable.values():
        for here, after in zip(cycle, cycle[1:] + cycle[:1]):
            successor[here] = states[after]

    rows = []
    for i, clause in enumerate(clauses):
        for j, literal in enumerate(clause):
            here = (i, j)
            t, u, mark = states[here], successor[here], markers[here]
            # Positive u=t OR mark, negative t=u AND NOT mark.
            rows.append(gate(t, mark, -u) if literal > 0 else gate(-u, mark, t))
        a, b, c, d, f, aux = [name() for _ in range(6)]
        rows.extend((gate(-f, -a, b), gate(-a, -c, d), gate(-b, -c, -d)))
        left, middle, right = (markers[i, j] for j in range(3))
        rows.extend((gate(left, middle, aux), gate(-aux, right, f)))
    return rows


def occurrence_audit():
    clauses = list(product(*[(i, -i) for i in range(1, 4)]))
    both = set()
    for mask in range(256):
        source = [clause for i, clause in enumerate(clauses) if mask & (1 << i)]
        # No, one, or all signs of the same proper triple. Every one of the
        # eight exclusions is needed for this family's single negative formula.
        for with_leaf in (False, True):
            formula = source + ([(1, -2, 4)] if with_leaf else [])
            rows = occurrence_two_rows(formula)
            assert all(len({v for v, _ in ports}) == 3 for _, ports in rows)
            counts = Counter(v for _, ports in rows for v, _ in ports)
            assert 0 not in counts and set(counts.values()) == {2}
            got = packed_decision(rows)[0]
            want = any(all(any(bool(x & (1 << (abs(l) - 1))) != (l < 0) for l in clause)
                           for clause in formula) for x in range(16))
            assert got == want
            both.add(got)
    assert both == {False, True}


def main():
    table_audit()
    occurrence_audit()
    rng = Random(34982)
    tables = [mask_of(vals) for vals in combinations(range(8), 4)]
    for _ in range(1200):
        rows = [(rng.choice(tables), tuple((rng.randrange(7), rng.randrange(2)) for _ in range(3)))
                for _ in range(rng.randrange(15))]
        assert packed_decision(rows)[0] == exhaustive_decision(rows)
    total = 0
    for p in (1, 2, 3):
        for t in range(1 << (1 << p)):
            for x in range(1 << p):
                result, width = packed_decision(table_membership(p, t, x))
                assert result == bool(t & (1 << x)) and width <= p + 1
                total += 1
    print("512 constant-free occurrence-two compilations passed, including SAT and UNSAT.")
    print("All 70 balanced tables classified: 12 both, 32 majority only, 2 affine only, 24 NOR.")
    print(f"1,200 signed-selector batches and {total:,} serialized membership cases passed.")


if __name__ == "__main__":
    main()
