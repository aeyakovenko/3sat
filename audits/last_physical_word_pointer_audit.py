"""Round 1. Check sparse pointer walks across native stores and last-word SAT files.

Run with python3 -B last_physical_word_pointer_audit.py from the clone.
"""

from collections import defaultdict, deque
from dataclasses import dataclass
from itertools import product
from random import Random

from table_probe_context_audit import parse, satisfiable


@dataclass(frozen=True)
class Label:
    depth: int
    cycle: int
    entry: int
    period: int
    first: int
    end: int


class OrbitIndex:
    """Old memory is a function on word values. Unlisted keys map to zero."""

    def __init__(self, memory):
        memory = {x: y for x, y in memory.items() if y}
        nodes = set(memory) | set(memory.values()) | {0}
        successor = {x: memory.get(x, 0) for x in nodes}
        children = defaultdict(list)
        for x, y in successor.items():
            children[y].append(x)
        indegree = {x: len(children[x]) for x in nodes}
        queue = deque(x for x in nodes if not indegree[x])
        peeled = []
        while queue:
            x = queue.popleft()
            peeled.append(x)
            y = successor[x]
            indegree[y] -= 1
            if not indegree[y]:
                queue.append(y)

        cyclic = nodes - set(peeled)
        self.labels = {}
        self.cycles = []
        self.jump = {}
        self.position = {}
        visited = 0

        def visit(x, depth, cycle, entry, period):
            nonlocal visited
            first = visited
            visited += 1
            for child in children[x]:
                if child not in cyclic:
                    visit(child, depth + 1, cycle, entry, period)
            self.labels[x] = Label(depth, cycle, entry, period, first, visited)

        for x in cyclic:
            if x in self.labels:
                continue
            ring = [x]
            y = successor[x]
            while y != x:
                ring.append(y)
                y = successor[y]
            for entry, root in enumerate(ring):
                visit(root, 0, len(self.cycles), entry, len(ring))
            self.cycles.append(ring)

        # Bender--Farach-Colton jump and ladder index on the forest.
        height = {x: 1 for x in nodes}
        heavy = {}
        for x in peeled:
            y = successor[x]
            if height[y] < 1 + height[x]:
                height[y] = 1 + height[x]
                heavy[y] = x
        for x in nodes:
            if x not in cyclic and heavy.get(successor[x]) == x:
                continue
            ladder = [x]
            while ladder[-1] in heavy:
                ladder.append(heavy[ladder[-1]])
            extra = []
            ancestor = x
            for _ in range(min(len(ladder), self.labels[x].depth)):
                ancestor = successor[ancestor]
                extra.append(ancestor)
            extended = extra[::-1] + ladder
            for i, member in enumerate(ladder, len(extra)):
                self.position[member] = extended, i
        for x in sorted(nodes, key=lambda key: self.labels[key].depth):
            jumps = []
            for j in range(self.labels[x].depth.bit_length()):
                jumps.append(successor[x] if j == 0 else self.jump[jumps[-1]][j-1])
            self.jump[x] = jumps

    def hits(self, x, steps, target):
        """Use only the labels of the origin, target, and zero."""
        if steps == 0:
            return x == target
        if x not in self.labels:
            return self.hits(0, steps - 1, target)
        a, b = self.labels[x], self.labels.get(target)
        if b is None or a.cycle != b.cycle:
            return False
        if steps < a.depth:
            return b.depth == a.depth - steps and b.first <= a.first < b.end
        return b.depth == 0 and (a.entry + steps - a.depth) % a.period == b.entry

    def advance(self, x, steps):
        if steps == 0:
            return x
        if x not in self.labels:
            return self.advance(0, steps - 1)
        label = self.labels[x]
        if steps >= label.depth:
            pos = (label.entry + steps - label.depth) % label.period
            return self.cycles[label.cycle][pos]
        j = steps.bit_length() - 1
        ladder, pos = self.position[self.jump[x][j]]
        offset = pos - (steps - (1 << j))
        assert offset >= 0
        return ladder[offset]


def deferred(index, start, writes, versions):
    """versions[i] is the count of earlier stores at the i-th dependent LOAD."""
    origin, skipped = start, 0
    for version in versions:
        # Latest earlier matching write wins. All store keys/payloads are resolved.
        for key, value in reversed(writes[:version]):
            if index.hits(origin, skipped, key):
                origin, skipped = value, 0
                break
        else:
            skipped += 1
    return index.advance(origin, skipped)


def eager(memory, start, writes, versions):
    view = memory.copy()
    applied = 0
    for version in versions:
        while applied < version:
            key, value = writes[applied]
            view[key] = value
            applied += 1
        start = view.get(start, 0)
    return start


def audit_walks():
    schedules = [(0, 1, 2), (0, 0, 1, 1, 2, 2), (0, 2, 2, 2, 2)]
    cases = 0
    for values in product(range(4), repeat=4):
        memory = dict(enumerate(values))
        index = OrbitIndex(memory)
        for start in range(6):
            now = start
            for steps in range(18):
                assert index.advance(start, steps) == now
                for target in range(6):
                    assert index.hits(start, steps, target) == (now == target)
                now = memory.get(now, 0)
        for writes in product(product(range(4), repeat=2), repeat=2):
            for start, versions in product(range(4), schedules):
                assert deferred(index, start, writes, versions) == eager(memory, start, writes, versions)
                cases += 1
    print("All 256 old four-word maps;", cases, "two-store pointer walks")
    rng = Random(1147)
    for _ in range(2000):
        memory = {x: rng.randrange(48) for x in rng.sample(range(64), 27)}
        index = OrbitIndex(memory)
        start = rng.randrange(80)
        writes = [(rng.randrange(80), rng.randrange(80)) for _ in range(24)]
        versions = sorted(rng.choices(range(25), k=100))
        assert deferred(index, start, writes, versions) == eager(memory, start, writes, versions)
        for steps in (3, 7, 31, 257):
            now = eager(memory, start, [], [0]*steps)
            assert index.advance(start, steps) == now and index.hits(start, steps, now)
    # Applying the newest snapshot to the entire lineage gives the wrong result.
    memory, writes = {0: 1, 1: 2}, [(0, 0)]
    assert deferred(OrbitIndex(memory), 0, writes, (0, 1)) == 2
    assert eager(memory, 0, writes, (1, 1)) == 0
    print("2,000 longer sparse histories; stale-snapshot counterexample 2 versus 0")


def audit_instructions():
    rng = Random(11415)
    charged = loads = 0
    for _ in range(256):
        memory = {x: rng.randrange(32) for x in rng.sample(range(32), 18)}
        index = OrbitIndex(memory)
        writes = []
        regs = [rng.randrange(32) for _ in range(8)]
        lazy = [(x, ()) for x in regs]
        # Forward branches can skip the next instruction. The STORE address
        # and payload may each still be a chain from an older memory version.
        code = [(rng.choice("LLLLLLCCASSB"), *rng.choices(range(8), k=3)) for _ in range(200)]
        pc = 0
        while pc < len(code):
            op, dest, a, b = code[pc]
            pc += 1
            if op == "L":
                regs[dest] = memory.get(regs[a], 0)
                start, versions = lazy[a]
                lazy[dest] = start, versions+(len(writes),)
                loads += 1
            elif op == "C":
                regs[dest], lazy[dest] = regs[a], lazy[a]
            else:
                charged += op == "S" or bool(lazy[a][1] or lazy[b][1])
                x, y = (deferred(index, lazy[i][0], writes, lazy[i][1]) for i in (a, b))
                assert (x, y) == (regs[a], regs[b])
                if op == "S":
                    memory[regs[a]] = regs[b]
                    writes.append((x, y))
                elif op == "A":
                    regs[dest] = (regs[a]+regs[b]) % 32
                    lazy[dest] = (x+y) % 32, ()
                else:
                    pc += x < y
    print("256 native instruction traces;", loads, "free LOADs;", charged, "charged instructions")


def audit_catalog():
    def sat(p, m):
        return any((p & ~a) == (m & a) == 0 for a in range(1, 4))

    for last_positive in (False, True):
        labels = [sat(x, 1) if last_positive else sat(1, x) for x in range(4)]
        assert labels == [True, False, True, False]
        for c in range(4):
            for key in (lambda x: x, lambda x: (x+2) % 4):
                for test in (lambda x: x == c, lambda x: key(x) < key(c),
                             lambda x: key(x) > key(c)):
                    assert any(test(x) == test(x+1) for x in (0, 2))
    for p, m in product(range(4), repeat=2):
        assert sat(p, m) == (m != 3 and p & m == 0)
    print("Both four-bit final-word cofactors, every unary native comparison")

    base = [1, 1, 2, 2]
    for last in range(4):
        delta = 2 if last < 2 else 1
        for i in range(4):
            row = base.copy()
            row[last] = delta*i
            p = row[0] + 16*row[1]
            m = row[2] + 16*row[3]
            assert (m != 255 and p & m == 0) == (i % 2 == 0)
        for c in range(16):
            for key in (lambda x: x, lambda x: (x+8) % 16):
                for test in (lambda x: x == c, lambda x: key(x) < key(c),
                             lambda x: key(x) > key(c)):
                    assert any(test(delta*i) == test(delta*(i+1)) for i in (0, 2))

    def nine_steps(p0, p1, m0, m1):
        # The two control paths are unrolled. Each return gives verdict,
        # elapsed steps, and the step of the fourth distinct LOAD, if any.
        if m0 == 15:                      # LOAD M0, compare
            if m1 == 15:                  # LOAD M1, compare
                return False, 4, None
            if p0 != 0:                   # LOAD P0, compare
                return False, 6, None
            return p1 & m1 == 0, 9, 7     # LOAD P1, AND, compare
        if p0 & m0:                       # LOAD P0, AND, compare
            return False, 5, None
        return p1 & m1 == 0, 9, 7         # LOAD P1, LOAD M1, AND, compare

    accepted = complete = 0
    for p0, p1, m0, m1 in product(range(16), repeat=4):
        p, m = p0 + 16*p1, m0 + 16*m1
        verdict, clock, last = nine_steps(p0, p1, m0, m1)
        assert verdict == any(p & ~a == m & a == 0 for a in range(1, 256))
        if last is not None:
            assert clock-last == 2
            complete += 1
        accepted += verdict
    assert (accepted, complete) == (6560, 20720)
    print("65,536 four-word inputs;", accepted, "SAT;", complete, "full reads with a two-step tail")


def clause(a, b, c):
    return f"{a} {b} {c} 0\n".encode()


def width(words):
    ell = 1
    while (1 << ell) < 1024 * ell * words + 2:
        ell += 1
    n = 1024 * ell * words
    assert ell == (n + 1).bit_length()
    return 128 * ell


class ButterflyFiles:
    def __init__(self, degree, depth):
        self.degree = degree
        self.depth = depth
        self.side = degree**depth
        self.vertices = (depth + 1) * self.side
        self.edges = degree * depth * self.side
        self.slots = self.edges + 1
        self.word_bytes = width(self.slots)
        self.public = [b"" for _ in range(self.slots)]
        self.public[0] = f"p cnf {3+2*self.vertices} {7+2*self.slots+2*self.vertices}\n".encode()
        for forbidden in range(1, 8):
            self.public[0] += clause(*(-i if forbidden & (1 << (i-1)) else i for i in (1, 2, 3)))
        for vertex in range(self.vertices):
            for flag in (0, 1):
                self.public[vertex] += clause(4+2*vertex+flag, -1, 2)

    def step(self, level, u, digit):
        place = self.degree**level
        return u + (digit - (u//place % self.degree)) * place

    def edge(self, number, present):
        row, digit = divmod(number, self.degree)
        level, u = divmod(row, self.side)
        v = self.step(level, u, digit)
        a = 4 + 2*row
        b = 4 + 2*((level+1)*self.side + v)
        return clause(-a, b+int(not present), 1) + clause(-a-1, b+1, 1)

    def query(self, s, t, b):
        return clause(4+2*s, 1, 2) + clause(-(4+2*(self.depth*self.side+t)+b), 1, 2)

    def reaches(self, mask, s, t):
        for level in range(self.depth):
            digit = t//self.degree**level % self.degree
            edge = (level*self.side+s)*self.degree + digit
            if not (mask >> edge) & 1:
                return False
            s = self.step(level, s, digit)
        return True

    def word(self, slot, payload):
        first, second = payload.splitlines(keepends=True)
        return self.half(self.public[slot] + first) + self.half(second)

    def half(self, raw):
        size = self.word_bytes // 2
        assert raw.endswith(b"\n") and len(raw) <= size
        return raw[:-1].ljust(size-1, b" ") + b"\n"


def audit_segments():
    """Lookup from the two raw last-word halves and the precomputed path pieces."""
    rng = Random(194)
    cases = 0
    for degree, depth in ((2, 3), (2, 5), (4, 2)):
        files = ButterflyFiles(degree, depth)
        first, second = {}, {}
        last = files.slots-1
        assert not files.public[last]
        cut = files.word_bytes//2
        for s in range(files.side):
            word = files.word(last, files.query(s, 0, 0))
            first[word[:cut]] = s
        for t, b in product(range(files.side), range(2)):
            word = files.word(last, files.query(0, t, b))
            second[word[cut:]] = t, b
        assert len(first) == files.side and len(second) == 2*files.side
        for mask in (0, (1 << files.edges)-1, rng.getrandbits(files.edges)):
            for bands in range(1, depth+1):
                bounds = [i*depth//bands for i in range(bands+1)]
                tables = []
                for lo, hi in zip(bounds, bounds[1:]):
                    table = {}
                    for u, digits in product(range(files.side), range(degree**(hi-lo))):
                        v = u
                        ok = True
                        for level in range(lo, hi):
                            digit = digits//degree**(level-lo) % degree
                            edge = (level*files.side+v)*degree+digit
                            ok &= bool(mask & (1 << edge))
                            v = files.step(level, v, digit)
                        table[u, digits] = ok
                    tables.append(table)
                for s, t, tag in product(range(files.side), range(files.side), range(2)):
                    word = files.word(last, files.query(s, t, tag))
                    source = first[word[:cut]]
                    sink, read_tag = second[word[cut:]]
                    present = True
                    for table, lo, hi in zip(tables, bounds, bounds[1:]):
                        place = degree**lo
                        u = source//place*place + sink % place
                        digits = sink//place % degree**(hi-lo)
                        present &= table[u, digits]
                    assert (present == bool(read_tag)) == (files.reaches(mask, s, t) == bool(tag))
                    cases += 1
    print(cases, "tagged half-word and segment-table queries")


def audit_files(depth, masks):
    files = ButterflyFiles(2, depth)
    pairs = 0
    last_positions = set()
    for mask in masks:
        edges = [files.edge(i, mask >> i & 1) for i in range(files.edges)]
        for order in ("forward", "reverse", "adaptive"):
            slots = list(range(files.slots))
            placed = [None] * files.slots
            cursor = 17
            for edge in edges:
                pos = 0 if order == "forward" else -1 if order == "reverse" else cursor % len(slots)
                slot = slots.pop(pos)
                placed[slot] = files.word(slot, edge)
                cursor = sum(placed[slot]) + slot
            last, = slots
            last_positions.add(last)
            for s, t in product(range(files.side), repeat=2):
                choices = [files.word(last, files.query(s, t, b)) for b in (0, 1)]
                assert sum((a ^ b).bit_count() for a, b in zip(*choices)) == 1
                for b, final in enumerate(choices):
                    placed[last] = final
                    raw = b"".join(placed)
                    assert len(raw) == files.slots * files.word_bytes
                    clauses, _ = parse(raw)
                    assert satisfiable(clauses) == (files.reaches(mask, s, t) == bool(b))
                pairs += 1
    print(f"Depth {depth}: {pairs} physical one-bit pairs, DPLL both ways, "
          f"{files.slots} words, {8*files.slots*files.word_bytes} bits, "
          f"last slots {sorted(last_positions)}")


if __name__ == "__main__":
    audit_catalog()
    audit_walks()
    audit_instructions()
    audit_files(1, range(16))
    audit_files(2, [0, 65535, 257, 32702])
    audit_segments()
