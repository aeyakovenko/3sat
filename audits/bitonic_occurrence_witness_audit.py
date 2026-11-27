#!/usr/bin/env python3
"""Audit a comment-free bitonic sorter and a numeric occurrence-witness pass.

B=2**b event records each contain b address bits, b timestamp bits and one
payload bit (width h=2*b+1). Sort on (address,time), moving the payload as
well. The actual query asks whether the least key has the asserted payload.
Every swap builds fresh Boolean gates even on known, equal or constant
values. The table reports g Boolean operation gates, m literal occurrences,
and N physical input bits including the header and final newline.

The ASCII emitter and the numeric replay run independently on public event
values and the proposed terminal payload. They share the numeric placement
algorithm and clause order. Numeric replay receives no file or parsed IDs,
formats no decimal names and outputs the underlying *variable* bit at each
occurrence. A separate checking routine uses the single parse of the real
file to enforce repeated-name consistency and interpret signs. Its acceptance
is sound for arbitrary proposed occurrences on that parsed proper formula.
"""

from collections import Counter
from itertools import product


def anchors():
    return [tuple(-i if mask & (1 << (i - 1)) else i for i in (1, 2, 3))
            for mask in range(1, 8)]


def gate_clauses(op, v, a, b):
    if op == "copy":
        return ((-v, a, 1), (v, -a, 1))
    if op == "and":
        return ((-v, a, 1), (-v, b, 1), (v, -a, -b))
    if op == "or":
        return ((v, -a, 1), (v, -b, 1), (-v, a, b))
    if op == "xor":
        return ((a, b, -v), (-a, -b, -v), (-a, b, v), (a, -b, v))
    raise ValueError(op)


class Layout:
    def __init__(self):
        self.last = 3
        self.ops = 0
        self.comparators = 0
        self.stages = 0

    def init(self):
        for clause in anchors():
            self.clause(clause)

    def pin(self, bit):
        self.last += 1
        self.save_input(bit)
        self.clause((self.last if bit else -self.last, 1, 2))
        return self.last

    def gate(self, op, a, b=0):
        self.last += 1
        self.ops += 1
        self.save_gate(op, a, b)
        for clause in gate_clauses(op, self.last, a, b):
            self.clause(clause)
        return self.last


class FileLayout(Layout):
    def __init__(self):
        super().__init__()
        self.body = bytearray()
        self.count = 0

    def clause(self, row):
        self.body.extend(b"%d %d %d 0\n" % row)
        self.count += 1

    def save_input(self, bit):
        pass

    def save_gate(self, op, a, b):
        pass

    def bytes(self):
        return b"p cnf %d %d\n" % (self.last, self.count) + self.body


class NumericLayout(Layout):
    def __init__(self):
        super().__init__()
        self.values = bytearray(4)  # index zero is unused; the anchors are false
        self.occurrences = bytearray()

    def clause(self, row):
        self.occurrences.extend(self.values[abs(lit)] for lit in row)

    def save_input(self, bit):
        self.values.append(bit)

    def signed(self, lit):
        return self.values[abs(lit)] ^ (lit < 0)

    def save_gate(self, op, a, b):
        x = self.signed(a)
        if op == "copy":
            result = x
        elif op == "and":
            result = x & self.signed(b)
        elif op == "or":
            result = x | self.signed(b)
        elif op == "xor":
            result = x ^ self.signed(b)
        else:
            raise ValueError(op)
        self.values.append(result)


def compare_swap(out, a, b, increasing, zero):
    """LSB-first record ids; bit zero travels as payload but never as a key."""
    delta = [out.gate("xor", x, y) for x, y in zip(a, b)]
    swap = zero
    for i in range(1, len(a)):
        x, y = (a[i], b[i]) if increasing else (b[i], a[i])
        higher_greater = out.gate("and", x, -y)
        lower_greater_on_tie = out.gate("and", -delta[i], swap)
        swap = out.gate("or", higher_greater, lower_greater_on_tie)
    first, second = [], []
    for i, different in enumerate(delta):
        flip = out.gate("and", different, swap)
        first.append(out.gate("xor", a[i], flip))
        second.append(out.gate("xor", b[i], flip))
    out.comparators += 1
    return first, second


def build(out, events, h, expected_payload, wrong=False):
    size = len(events)
    if size < 2 or size & (size - 1) or h < 2:
        raise ValueError("need a nontrivial power-of-two event count and width at least two")
    if any(n < 0 or n >= 1 << h for n in events) or expected_payload not in (0, 1):
        raise ValueError("value outside event or payload width")
    out.init()
    zero = out.pin(0)
    lanes = [[out.pin((r >> j) & 1) for j in range(h)] for r in events]
    length = 2
    while length <= size:
        dist = length >> 1
        while dist:
            out.stages += 1
            for i in range(size):
                j = i ^ dist
                if i < j:
                    lanes[i], lanes[j] = compare_swap(out, lanes[i], lanes[j], (i & length) == 0, zero)
            dist >>= 1
        length <<= 1

    endpoint = lanes[0][0] if expected_payload else -lanes[0][0]
    # An adjacent even/odd pair differs only in its final decimal digit. Any
    # extra copy is on the terminal dependency path and costs one fixed gate.
    if (out.last + 1) & 1:
        endpoint = out.gate("copy", endpoint)
    good = out.gate("copy", endpoint)
    bad = out.gate("copy", -good)
    out.clause((bad if wrong else good, 1, 2))
    return lanes


class Formula:
    def __init__(self, raw):
        lines = raw.splitlines()
        head = lines[0].split()
        if len(head) != 4 or head[:2] != [b"p", b"cnf"]:
            raise ValueError("missing DIMACS header")
        self.variables, count = map(int, head[2:])
        if len(lines) != count + 1:
            raise ValueError("wrong clause count")
        self.clauses = []
        seen, names = set(), set()
        for line in lines[1:]:
            a, b, c, end = map(int, line.split())
            row = a, b, c
            key = tuple(sorted(row))
            if end or len({abs(a), abs(b), abs(c)}) != 3 or key in seen:
                raise ValueError("improper or duplicated clause")
            seen.add(key)
            names.update(map(abs, row))
            self.clauses.append(row)
        if names != set(range(1, self.variables + 1)):
            raise ValueError("variable names must be dense and within the declared range")

    def validate(self, occurrences):
        """One shared parse, O(m) per trial, fresh/dense scratch at most O(m)."""
        if len(occurrences) != 3 * len(self.clauses):
            return False
        names = bytearray([2]) * (self.variables + 1)
        pos = 0
        for row in self.clauses:
            ok = False
            for lit in row:
                b = occurrences[pos]
                pos += 1
                v = abs(lit)
                if b not in (0, 1) or (names[v] != 2 and names[v] != b):
                    return False
                names[v] = b
                ok |= b == (lit > 0)
            if not ok:
                return False
        return True

    def forced_verdict(self):
        """Independent SAT/UNSAT check: fix exactly the seven anchor constraints'
        unique solution, then deduce only forced units in formula order."""
        for trial in product((0, 1), repeat=3):
            allowed = all(any(trial[abs(l) - 1] == (l > 0) for l in c) for c in self.clauses[:7])
            assert allowed == (trial == (0, 0, 0))
        values = {1: 0, 2: 0, 3: 0}
        for row in self.clauses[7:]:
            pending = [v for v in row if abs(v) not in values]
            if any(values.get(abs(l), 2) == (l > 0) for l in row):
                continue
            if not pending:
                return False
            if len(pending) == 1:
                lit = pending[0]
                values[abs(lit)] = int(lit > 0)
        assert len(values) == self.variables
        assert all(any(values[abs(l)] == (l > 0) for l in row) for row in self.clauses)
        return True


def numeric_pass(events, h, expected, wrong=False):
    replay = NumericLayout()
    lanes = build(replay, events, h, expected, wrong)
    return replay, [sum(replay.values[name] << j for j, name in enumerate(row)) for row in lanes]


def full_check(events, h):
    b = len(events).bit_length() - 1
    expect_sorted = sorted(events, key=lambda v: v >> 1)
    expected = expect_sorted[0] & 1
    replay, ordered = numeric_pass(events, h, expected)
    assert ordered == expect_sorted  # timestamps in the full-file fixtures are unique
    size = len(events)
    assert replay.stages == b * (b + 1) // 2
    assert replay.comparators == size * replay.stages // 2
    assert replay.ops - replay.comparators * (4 * h + 3 * (h - 1)) in (2, 3)

    raws = []
    for wrong in (False, True):
        emitter = FileLayout()
        build(emitter, events, h, expected, wrong)
        raw = emitter.bytes()
        parsed = Formula(raw)  # exactly one parse for all trials on this input
        assert parsed.forced_verdict() == (not wrong)
        assert parsed.validate(replay.occurrences) == (not wrong)
        wrong_replay, _ = numeric_pass(events, h, expected, wrong)
        assert parsed.validate(wrong_replay.occurrences) == (not wrong)
        damaged = replay.occurrences.copy()
        damaged[-2] ^= 1  # disagree with earlier occurrences of anchor 1
        assert not parsed.validate(damaged)
        raws.append(raw)

    assert len(raws[0]) == len(raws[1]) and sum(x != y for x, y in zip(*raws)) == 1
    m, n_bits = len(replay.occurrences), 8 * len(raws[0])
    assert 6 * replay.ops <= m <= 12 * replay.ops + 3 * (size * h + 9)
    # This measurement is outside numeric replay. Every operation output is
    # distinct and appears, so just spelling its name once gives a lower bound.
    first_gate = 5 + size * h
    assert n_bits >= 8 * sum(len(str(i)) for i in range(first_gate, replay.last + 1))
    return replay.stages, replay.comparators, replay.ops, m, n_bits


def main():
    total = 0
    # Four choices (address bit, payload bit) per event; the timestamp is its
    # actual input position. Check every case at sizes two and four.
    for b in (1, 2):
        for choices in product(range(4), repeat=1 << b):
            events = [((choice >> 1) << (b + 1)) | (time << 1) | (choice & 1)
                      for time, choice in enumerate(choices)]
            ref = sorted(events, key=lambda v: v >> 1)
            _, result = numeric_pass(events, b + 2, ref[0] & 1)
            assert ref == result
            total += 1
    # Include tied keys with differing payloads; only key order and record
    # multiset are specified when timestamps tie.
    for events in product(range(4), repeat=4):
        _, result = numeric_pass(events, 2, 0)
        assert [v >> 1 for v in result] == sorted(v >> 1 for v in events)
        assert Counter(result) == Counter(events)
        total += 1
    print("B h stages comparators g m N_bits")
    for b in range(1, 6):
        size, h = 1 << b, 2 * b + 1
        events = [(((7 * t + t // 2 + 3) % size) << (b + 1)) | (t << 1) | ((t ^ (t >> 1)) & 1)
                  for t in range(size)]
        print(size, h, *full_check(events, h))
    print("PASS:", total, "exhaustive numeric inputs; five proper SAT/UNSAT file pairs, one byte edit each")


if __name__ == "__main__":
    main()
