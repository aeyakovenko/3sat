"""Exhaust small alleged RAM histories against independent native execution.

The file construction and its asymptotic size are proved in the manuscript.
Here a prefix describes a claimed controller and the store stamp at its load.
"""
from itertools import product

OPS = ("flip", "input", "store0", "store1", "load", "branch", "yes", "no")
START = (0, 0)
NO, YES = -1, -2
DEFAULT, INIT = -2, -1


def next_state(program, bits, before, reply=None):
    pc, reg = before
    if pc < 0:
        return before
    op = program[pc]
    nxt = (pc + 1) % len(program)
    if op == "flip":
        return nxt, reg ^ 1
    if op == "input":
        return nxt, bits[reg]
    if op == "load":
        return nxt, reply
    if op == "branch":
        return (pc + 1 + reg) % len(program), reg
    if op in ("yes", "no"):
        return (YES if op == "yes" else NO), reg
    return nxt, reg


def native(program, bits, clock):
    memory = [(INIT, 0), (INIT, 0)]
    controller = [START]
    stamps = []
    for t in range(clock):
        pc, reg = state = controller[-1]
        op = program[pc] if pc >= 0 else "idle"
        stamp, value = DEFAULT, None
        if op == "load":
            stamp, value = memory[reg]
        if op in ("store0", "store1"):
            memory[reg] = t, int(op[-1])
        controller.append(next_state(program, bits, state, value))
        stamps.append(stamp)
    return tuple(controller), tuple(stamps)


def has_defect(program, bits, states, stamps):
    if states[0] != START or states[-1][0] != NO:
        return True
    for t, (before, after, stamp) in enumerate(zip(states, states[1:], stamps)):
        pc, reg = before
        op = program[pc] if pc >= 0 else "idle"
        if after != next_state(program, bits, before, after[1]):
            return True
        if op != "load":
            if stamp != DEFAULT:
                return True
            continue
        if not INIT <= stamp < t:
            return True

        def stores_at(j):
            addr_pc, addr = states[j]
            return addr_pc >= 0 and addr == reg and program[addr_pc] in ("store0", "store1")

        if stamp == INIT:
            if after[1] != 0:
                return True
        elif not stores_at(stamp) or int(program[states[stamp][0]][-1]) != after[1]:
            return True
        if any(stores_at(j) for j in range(stamp + 1, t)):
            return True
    return False


def alleged(program, bits, clock):
    def extend(states, stamps):
        t = len(stamps)
        if t == clock:
            yield tuple(states), tuple(stamps)
            return
        pc, _ = state = states[-1]
        if pc >= 0 and program[pc] == "load":
            choices = product((0, 1), range(INIT, t))
        else:
            choices = ((None, DEFAULT),)
        for value, stamp in choices:
            yield from extend(states + [next_state(program, bits, state, value)], stamps + [stamp])

    return extend([START], [])


def audit_histories():
    runs = histories = accepted = 0
    for program in product(OPS, repeat=3):
        for bits in product((0, 1), repeat=2):
            true_states, true_sources = native(program, bits, 4)
            for states, sources in alleged(program, bits, 4):
                valid = not has_defect(program, bits, states, sources)
                expected = states[-1][0] == NO and (states, sources) == (true_states, true_sources)
                assert valid == expected
                histories += 1
                accepted += valid
            runs += 1
    # Earlier stores of the same value are still stale sources.
    p = ("store0", "store0", "load", "no")
    states, sources = native(p, (0, 1), 4)
    assert not has_defect(p, (0, 1), states, sources)
    assert has_defect(p, (0, 1), states, (DEFAULT, DEFAULT, 0, DEFAULT))
    print(f"{runs} bounded native runs, {histories} proposed histories, "
          f"{accepted} valid rejecting histories")


def audit_reports():
    # Two described trials, one per large-input reporter. The true local test
    # is positive exactly when the claimed rejecting history is invalid.
    cases = removals = misses = 0
    for large in product((0, 1), repeat=2):
        for exact in product((0, 1), repeat=2):
            if any(exact[i] and not large[i] for i in range(2)):
                continue
            for votes in product((0, 1), repeat=4):
                active = [0, 1]
                while True:
                    witness = next(((i, j) for i in active for j in active if votes[2*j+i]), None)
                    if witness is None:
                        for i in active:
                            if exact[i]:
                                assert all(not votes[2*j+i] for j in active)
                                misses += 1
                        break
                    i, j = witness
                    if large[i]:  # a real NO on the positive outer trial
                        retire = i
                    else:
                        assert not exact[i] and votes[2*j+i]  # a real NO on a positive test
                        retire = j
                    active.remove(retire)
                    removals += 1
                cases += 1
    print(f"{cases} two-reporter tables, {removals} removals, {misses} terminal described misses")


def first_missing(rows, count):
    # A bit mask is exactly the columns already used by one prefix matching.
    matchings = {0}
    for rank, neighbors in enumerate(rows):
        extended = {used | (1 << col) for used in matchings for col in range(count)
                    if neighbors & (1 << col) and not (used & (1 << col))}
        if not extended:
            return rank, matchings
        matchings = extended
    return len(rows), matchings


def audit_ranks():
    count = 4
    graphs = 0
    for rows in product(range(1 << count), repeat=count):
        rank, before = first_missing(rows, count)
        if rank < count:
            for col in range(count):
                if rows[rank] & (1 << col):
                    assert all(used & (1 << col) for used in before)
                    assert any(rows[s] & (1 << col) for s in range(rank))
        graphs += 1
    for hole in range(count):
        rows = [int(s != hole) << s for s in range(count)]
        assert first_missing(rows, count)[0] == hole
    print(f"{graphs} four-column graphs, all four private-edge holes")


if __name__ == "__main__":
    audit_histories()
    audit_reports()
    audit_ranks()
