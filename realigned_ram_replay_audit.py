"""Compare indexed replay on an implicit edited run with an independent edit-distance DP."""
from bisect import bisect_left
from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass(frozen=True)
class Record:
    before: tuple
    event: str
    address: int
    value: int
    after: tuple


def execute(program, ctrl, read):
    pc, a, b = ctrl
    op, arg = program[pc]
    event, address, value = "-", -1, 0
    pc += 1
    if op == "load":
        event, address = "r", (b + arg) % 8
        a = value = read(address)
    elif op == "write":
        event, address, value = "w", (b + arg) % 8, a
    elif op == "a":
        a = arg
    elif op == "b":
        b = arg
    elif op == "add":
        a = (a + arg) % 8
    elif op == "swap":
        a, b = b, a
    elif op == "jump_if":
        if a:
            pc = arg
    else:
        raise ValueError(op)
    return Record(ctrl, event, address, value, (pc, a, b))


def full_run(program, data):
    memory = list(data)
    ctrl = (0, 0, 0)
    result = []
    while ctrl[0] < len(program):
        rec = execute(program, ctrl, memory.__getitem__)
        if rec.event == "w":
            memory[rec.address] = rec.value
        result.append(rec)
        ctrl = rec.after
        assert len(result) <= 256
    return result


class Index:
    def __init__(self, program, data):
        self.program, self.data = program, data
        self.trace = full_run(program, data)
        self.limit = len(self.trace)
        self.access, self.writes = defaultdict(list), defaultdict(list)
        for i, rec in enumerate(self.trace):
            if rec.event != "-":
                self.access[rec.address].append(i)
            if rec.event == "w":
                self.writes[rec.address].append(i)
        self.probes = 0

    def value(self, i, addr):
        self.probes += 1
        times = self.writes[addr]
        pos = bisect_left(times, i)
        return self.trace[times[pos - 1]].value if pos else self.data[addr]

    def deadline(self, i, addr, value):
        self.probes += 1
        times = self.access[addr]
        pos = bisect_left(times, i)
        inf = self.limit + 1
        if pos == len(times):
            return value, inf, inf
        j = times[pos]
        return (value, j + 1, inf) if self.trace[j].event == "w" else (value, inf, j)


@dataclass
class Cursor:
    i: int
    j: int
    ctrl: tuple
    changes: dict
    script: tuple


def replay(index, edits):
    # The edited trace itself is never read by this routine.
    d0 = {addr: index.deadline(0, addr, val) for addr, val in edits.items()
          if val != index.data[addr]}
    limit = index.limit

    def jump(s):
        if s.i == limit or index.trace[s.i].before != s.ctrl:
            return s
        # Heap minimum in the paper. Here integer comparisons on already held
        # appointments are free of old-index reads.
        stop = min([limit] + [entry[2] for entry in s.changes.values()])
        assert stop >= s.i
        if stop == s.i:
            return s
        return Cursor(stop, s.j + stop - s.i, index.trace[stop-1].after, s.changes, s.script)

    def advance(s, consume_old):
        i, j, ctrl, changes = s.i, s.j, s.ctrl, s.changes.copy()

        def peek(addr):
            if addr in changes:
                val, expires, _ = changes[addr]
                if i < expires:
                    return val
            return index.value(i, addr)

        def track(start, addr, newval, oldval):
            if newval == oldval:
                changes.pop(addr, None)
            else:
                changes[addr] = index.deadline(start, addr, newval)

        if consume_old:
            if i == limit:
                return None
            rec = index.trace[i]
            if rec.event == "w":
                track(i+1, rec.address, peek(rec.address), rec.value)
            elif rec.event == "r" and rec.address in changes:
                track(i+1, rec.address, peek(rec.address), rec.value)
            return Cursor(i+1, j, ctrl, changes, s.script + (("del", i, None),))
        if ctrl[0] >= len(index.program):
            return None
        rec = execute(index.program, ctrl, peek)
        if rec.event == "w":
            track(i, rec.address, rec.value, index.value(i, rec.address))
        return Cursor(i, j+1, rec.after, changes, s.script + (("ins", i, rec),))

    front = {0: jump(Cursor(0, 0, (0, 0, 0), d0, ()))}
    states = 1
    while front:
        for s in front.values():
            if s.i == limit and s.ctrl[0] >= len(index.program):
                return s, states
        candidates = {}
        for s in front.values():
            for consume in (True, False):
                nxt = advance(s, consume)
                if nxt is None:
                    continue
                k = nxt.i - nxt.j
                if k not in candidates or nxt.i > candidates[k].i:
                    candidates[k] = nxt
        front = {k: jump(s) for k, s in candidates.items()}
        states += len(front)
    raise AssertionError("missing endpoint")


def apply_script(old, script):
    out = []
    start = 0
    for op, place, rec in script:
        assert place >= start
        out.extend(old[start:place])
        if op == "ins":
            out.append(rec)
            start = place
        else:
            start = place+1
    return out + old[start:]


def independent_distance(left, right):
    row = list(range(len(right)+1))
    for i, a in enumerate(left, 1):
        nxt = [i]
        for j, b in enumerate(right, 1):
            nxt.append(min(1+nxt[-1], 1+row[j], row[j-1]+(0 if a == b else 2)))
        row = nxt
    return row[-1]


def check(program, base, edits):
    index = Index(program, base)
    state, states = replay(index, edits)
    new = list(base)
    for addr, value in edits.items():
        new[addr] = value
    truth = full_run(program, new)
    d = len(state.script)
    assert d == independent_distance(index.trace, truth)
    assert apply_script(index.trace, state.script) == truth
    assert state.j == len(truth)
    assert states <= (d+1)*(d+2)//2
    assert index.probes <= 12*(states + len(edits) + 1)
    return d


if __name__ == "__main__":
    # The only changed input sets the number of loop iterations.
    loop = [('load', 0), ('add', 7), ('write', 1), ('jump_if', 1),
            ('load', 2), ('add', 1), ('write', 3), ('load', 1)]
    trials = 0
    for initial, x, y in product(range(1,8), range(1,8), range(4)):
        check(loop, [initial, 4, 0, 1, 2, 3, 4, 5], {0:x, 2:y})
        trials += 1
    rng = Random(734158)
    for n in range(2, 27):
        for _ in range(65):
            program = []
            for i in range(n):
                op = rng.choice(('a', 'b', 'load', 'load', 'write', 'swap', 'jump_if', 'add'))
                arg = rng.randint(i+1,n) if op == 'jump_if' else rng.randrange(8)
                program.append((op, arg))
            base = [rng.randrange(8) for _ in range(8)]
            edits = {rng.randrange(8):rng.randrange(8) for _ in range(rng.randrange(4))}
            check(program, base, edits)
            trials += 1
    # Lose an arbitrarily long common suffix under same-timestamp comparison.
    suffix = [('add', 1), ('add', 7)] * 98
    example = [('load', 0), ('jump_if', 3), ('a', 0), ('a', 0)] + suffix
    a = full_run(example, [0]*8)
    b = full_run(example, [1]+[0]*7)
    delta = check(example, [0]*8, {0:1})
    mismatches = sum(i >= len(a) or i >= len(b) or a[i] != b[i]
                     for i in range(max(len(a), len(b))))
    print(f"{trials} loop and forward-control pairs agreed with the explicit edit-distance DP.")
    print(f"Shifted-suffix example: {mismatches} aligned mismatches, insertion/deletion distance {delta}.")
