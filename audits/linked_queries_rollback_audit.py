"""Check feedback, compact CNFs and first-read rollback on actual finite programs."""

from itertools import product
from random import Random


def reverse(value, bits):
    return int(f"{value:0{bits}b}"[::-1], 2)


def linked(records, bits, flip=None):
    arr = [0] * (1 << bits)
    prev = feedback = 0
    result = []
    for i, (value, endpoint, lane, salt) in enumerate(records):
        arr[reverse(i, bits)] = value
        ordinary = 0
        for v in arr[:endpoint + 1]:
            ordinary ^= v >> lane & 1
        # Left endpoint -1 places an all-ones word in the physical interval.
        selected = ordinary ^ feedback
        feedback = selected ^ prev ^ salt ^ ((endpoint.bit_count() + lane.bit_count()) & 1)
        if i == flip:
            feedback ^= 1
        prev = ordinary
        result.append(feedback)
    return result


def compile_cnf(records, bits):
    """Return the stopped-prefix clauses and the ID of the final verdict wire."""
    m = 1 << bits
    endpoint, lane = records[-1][1:3]
    clauses = []
    last_var = 0

    def fresh():
        nonlocal last_var
        last_var += 1
        return last_var

    def pin(a, val):
        clauses.append((a if val else -a,))

    def xor(a, b):
        c = fresh()
        clauses.extend(((-a, -b, -c), (-a, b, c), (a, -b, c), (a, b, -c)))
        return c

    def both(a, b):
        c = fresh()
        clauses.extend(((-a, -b, c), (a, -c), (b, -c)))
        return c

    sel = [fresh() for _ in range(bits)]
    pin(sel[lane], True)
    for i in range(bits):
        for j in range(i):
            clauses.append((-sel[j], -sel[i]))
    table = [fresh()]
    pin(table[0], False)
    for v in range(1, m):
        table.append(xor(table[v & (v - 1)], sel[(v & -v).bit_length() - 1]))
    d = [fresh() for _ in range(m)]
    for v in range(m):
        pin(d[v], v.bit_count() & 1)
    bounds = [fresh() for _ in range(m + 1)]
    for i in range(m):
        clauses.append((-bounds[i + 1], bounds[i]))
    pin(bounds[endpoint], True)
    pin(bounds[endpoint + 1], False)
    arr = [0] * m
    for i, record in enumerate(records):
        arr[reverse(i, bits)] = record[0]
    out = table[0]
    for pos, value in enumerate(arr):
        out = xor(out, both(bounds[pos], table[value]))
    for i in range(m):
        _, r, k, e = records[i] if i < len(records) else (0, 0, 0, 0)
        salt = fresh()
        pin(salt, e)
        out = xor(xor(xor(out, d[r]), d[k]), salt)
    return clauses, out


def propagate(clauses, out):
    values = {}
    while True:
        changes = 0
        for c in clauses:
            remaining = [lit for lit in c if abs(lit) not in values]
            if any(values[abs(lit)] == (lit > 0) for lit in c if abs(lit) in values):
                continue
            assert remaining
            if len(remaining) == 1:
                lit = remaining[0]
                values[abs(lit)] = lit > 0
                changes += 1
        if not changes:
            return int(values[out])


def native(view, regs=("end", 0, 0, 0, 0), work=(0, 0)):
    """Yield read site and post-state of a word program with writable scratch."""
    while regs[0] != "halt":
        op, i, endpoint, lane, val = regs
        site = None
        if op == "end":
            site, regs = 0, ("lane", 0, view[0], 0, 0)
        elif op == "lane":
            site, regs = 1, ("payload", 0, endpoint, view[1], 0)
        elif op == "payload":
            site = i + 2
            regs = ("store", i, endpoint, lane, view[site])
        elif op == "store":
            bank = i % 2
            changed = list(work)
            changed[bank] ^= val
            work = tuple(changed)
            regs = ("out" if i == endpoint else "payload", i + 1, endpoint, lane, 0)
        else:
            regs = ("halt", 0, 0, 0, ((work[0] ^ work[1]) >> lane) & 1)
        yield site, regs, work


def replay(rng):
    total = 0
    m = 12
    initial = (("end", 0, 0, 0, 0), (0, 0))
    for _ in range(45):
        view = [0, 0] + [0] * m
        trace = list(native(view))
        executed = len(trace)
        undone = 0
        for _ in range(75):
            edits = {rng.randrange(2, 2 + m): rng.randrange(64)}
            if rng.randrange(2):
                edits[rng.randrange(2)] = rng.randrange(6)
            changed = {a for a, v in edits.items() if view[a] != v}
            cut = next((j for j, e in enumerate(trace) if e[0] in changed), len(trace))
            undone += len(trace) - cut
            start = trace[cut - 1][1:] if cut else initial
            for a, new in edits.items():
                view[a] = new
            appended = list(native(view, *start))
            executed += len(appended)
            trace = trace[:cut] + appended
            assert trace == list(native(view))
            assert executed == len(trace) + undone
            total += 1
    return total


def main():
    rng = Random(71521)
    streams = 0
    tiny = list(product(range(2), range(2), (0,), range(2)))
    for bits in (1, 2, 3):
        m = 1 << bits
        if bits == 1:
            cases = product(tiny, repeat=m)
        else:
            cases = [[(rng.randrange(m), rng.randrange(m), rng.randrange(bits), rng.randrange(2))
                      for _ in range(m)] for _ in range(65)]
        for sequence in cases:
            answers = linked(sequence, bits)
            for i, answer in enumerate(answers):
                cs, out = compile_cnf(sequence[:i + 1], bits)
                assert propagate(cs, out) == answer
                assert linked(sequence, bits, i) == answers[:i] + [1 - b for b in answers[i:]]
                streams += 1
    print(f"{streams} stopped-prefix CNFs and feedback interventions; {replay(rng)} native rollbacks")


if __name__ == "__main__":
    main()
