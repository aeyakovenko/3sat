#!/usr/bin/env python3
"""Check every width of a proposed folded GF(2) pin certificate.

Run --example for a complete input, --self-test for calibration, or pass a JSON
file (use - for stdin). Columns are read LSB first within all base-B digits in
parallel. Matrices are lists of bit-packed rows, indexed first by column
symbol. A named schedule is prefix + loop*k + suffix, k >= 0, and B=2**h
where h is its length. All masks use coordinate 0 as their least significant
bit. Pin entries are terminal column masks for the shared weighted automaton:
pin i is set iff the scalar product of the final row and sink i is odd.
Use block-diagonal matrices and concatenate start rows for independent WFAs.

An input [gate,c,d] reads gate at u-(c+d*B). Negative times are zero except
for each gate's listed negative one-seeds. At lag zero the source must precede
the destination in the gate list. Truth-table indices use input 0 as the low
bit. Gates occur in list order at each timestamp. By default all gates through
the horizon are checked. Optional last_gate truncates the final timestamp after
that gate (the terminal gate must still be included). Horizon coefficients are
low to high. Bad geometry is reported even if a proposed certificate is empty.

A loop-boundary state consists of the GF(2) rows, the signed constant digit
streams, bounded comparisons, and borrow hypotheses for delayed timestamps.
Each signed digit register halves on every layer and eventually becomes 0 or
-1. All other registers have finite domains. To subtract a lag, guess the
incoming borrow of each digit after the first, do all single-bit subtractions,
and at the end match the adjacent outgoing and incoming borrows. Low-to-high
subtraction makes the compatible guess unique. A surviving final borrow
selects the fixed negative-time seeds. Below the symbolic sign-stability
threshold the checker normalizes constants separately in each concrete base.

Exploring each reachable loop-boundary state once suffices: continuation
matrices and the suffix test depend only on that state. A counterexample
decodes to a width and timestamp and is rechecked with integer arithmetic.
This algorithm can require exponentially many states and tests certificates
only; it does not synthesize the pins. Exit status is 0 for a certificate,
1 for a failing input, and argparse uses 2 for command-line usage errors.
"""

import argparse
import json
import random
import sys


def polynomial(coeffs, base):
    value = 0
    for coefficient in reversed(coeffs):
        value = value * base + coefficient
    return value


def trim(coeffs):
    result = list(coeffs)
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def shift_constant(coeffs, amount):
    return trim(((coeffs[0] if coeffs else 0) + amount, *coeffs[1:]))


def row_times(row, matrix):
    value = 0
    while row:
        bit = row & -row
        value ^= matrix[bit.bit_length() - 1]
        row ^= bit
    return value


class Instance:
    def __init__(self, data):
        self.blocks = data["blocks"]
        width = data["width"]
        if type(self.blocks) is not int or self.blocks < 1 or type(width) is not int or width < 1:
            raise ValueError("blocks and width must be positive integers")
        self.mask = (1 << self.blocks) - 1
        self.start = data["start"]
        self.layers = data["layers"]
        self.prefix, self.loop, self.suffix = (tuple(data[key]) for key in ("prefix", "loop", "suffix"))
        if not self.loop or any(k not in self.layers for k in self.prefix + self.loop + self.suffix):
            raise ValueError("schedule needs known layers and a nonempty loop")

        def check_mask(value):
            if type(value) is not int or not 0 <= value < (1 << width):
                raise ValueError("matrix or vector mask out of range")
        check_mask(self.start)
        for layer in self.layers.values():
            if len(layer) != self.mask + 1 or any(len(m) != width for m in layer):
                raise ValueError("wrong matrix or alphabet size")
            for matrix in layer:
                for row in matrix:
                    check_mask(row)

        gates = data["gates"]
        self.names = [g["name"] for g in gates]
        if len(set(self.names)) != len(gates):
            raise ValueError("gate names must be distinct")
        self.inputs, self.tables, self.pins, self.seeds = [], [], [], []
        for g in gates:
            edges = []
            for name, c, d in g["inputs"]:
                if type(c) is not int or type(d) is not int:
                    raise ValueError("lag coefficients must be integers")
                edges.append((self.names.index(name), trim((c, d))))
            table = g["table"]
            if len(table) != 1 << len(edges) or any(c not in "01" for c in table):
                raise ValueError("truth table needs one bit per input assignment")
            pins = g["pins"]
            if len(pins) != 2:
                raise ValueError("two sink masks required")
            for p in pins:
                check_mask(p)
            seeds = frozenset(g.get("seeds", []))
            if any(type(v) is not int or v >= 0 for v in seeds):
                raise ValueError("one-seeds must have negative integer timestamps")
            self.inputs.append(tuple(edges))
            self.tables.append(table)
            self.pins.append(pins)
            self.seeds.append(seeds)
        terminal = data["terminal"]
        self.terminal = self.names.index(terminal["gate"])
        self.value = terminal["value"]
        self.horizon = trim(terminal["horizon"])
        if any(type(v) is not int for v in self.horizon) or len(self.horizon) > self.blocks + 1:
            raise ValueError("horizon needs integer coefficients of degree at most blocks")
        if self.value not in (0, 1):
            raise ValueError("terminal value must be a bit")
        self.last = self.names.index(data["last_gate"]) if "last_gate" in data else len(gates) - 1
        if self.terminal > self.last:
            raise ValueError("terminal lies after last gate")
        self.lags = tuple(sorted({lag for edges in self.inputs for _, lag in edges}))
        self.seed_points = {(g, lag): tuple(shift_constant(lag, s) for s in self.seeds[g])
                            for edges in self.inputs for g, lag in edges}
        forms = {self.horizon, *self.lags, *(point for points in self.seed_points.values() for point in points)}
        # Above this bound, each normalized digit of every form, including
        # differences of two forms, is a small signed constant modulo B.
        self.safe_h = (2 + 2 * max(sum(map(abs, f)) for f in forms)).bit_length()
        self.comparisons = tuple(sorted({self.horizon, *(p for v in self.seed_points.values() for p in v)}))
        self.forms = tuple(sorted(forms))
        self.index = {f: i for i, f in enumerate(self.forms)}

    def geometry(self, h):
        base = 1 << h
        horizon = polynomial(self.horizon, base)
        if not 0 <= horizon < base ** self.blocks:
            return "horizon is outside the folded range"
        for g, edges in enumerate(self.inputs):
            for source, lag in edges:
                delay = polynomial(lag, base)
                if delay < 0 or (delay == 0 and source >= g):
                    return "gate %s has a future or unordered same-time input" % self.names[g]
        return None

    def check_pins(self, horizon_cmp, raw, predecessor, alias):
        """Concrete semantics shared by the arithmetic automaton and scalar oracle."""
        if horizon_cmp > 0:
            return None
        last = self.last if horizon_cmp == 0 else len(self.names) - 1
        for g in range(last + 1):
            pins = raw(g)
            if pins == (1, 1):
                return (self.names[g], "overlapping pins")
            if pins == (0, 0):
                continue
            claimed = pins[1]
            edges = self.inputs[g]
            # Repeated occurrences of the same predecessor denote one bit.
            keys = [alias(source, lag) for source, lag in edges]
            for n, out in enumerate(self.tables[g]):
                if int(out) == claimed:
                    continue
                assigned = {}
                for j, (source, lag) in enumerate(edges):
                    bit = (n >> j) & 1
                    p0, p1 = predecessor(source, lag)
                    if (p1 if bit == 0 else p0) or assigned.setdefault(keys[j], bit) != bit:
                        break
                else:
                    return (self.names[g], "gate rule fails on predecessor assignment %d" % n)
        if horizon_cmp == 0 and not raw(self.terminal)[self.value]:
            return (self.names[self.terminal], "terminal pin missing")
        return None

    def read_row(self, time, schedule):
        h = len(schedule)
        row = self.start
        for j, layer in enumerate(schedule):
            symbol = sum(((time >> (h * i + j)) & 1) << i for i in range(self.blocks))
            row = row_times(row, self.layers[layer][symbol])
        return row

    def read_pins(self, gate, row):
        return tuple((row & m).bit_count() % 2 for m in self.pins[gate])

    def scalar_at(self, schedule, u):
        h = len(schedule)
        base = 1 << h
        horizon = polynomial(self.horizon, base)
        rows = {u: self.read_row(u, schedule)}

        def parent(g, lag):
            v = u - polynomial(lag, base)
            if v < 0:
                bit = int(v in self.seeds[g])
                return (1 - bit, bit)
            if v not in rows:
                rows[v] = self.read_row(v, schedule)
            return self.read_pins(g, rows[v])
        return self.check_pins((u > horizon) - (u < horizon),
                               lambda g: self.read_pins(g, rows[u]), parent,
                               lambda g, lag: (g, polynomial(lag, base)))


class Folded:
    """Finite deterministic product transducer for all sufficiently large bases."""
    def __init__(self, instance, fixed_base=None):
        self.p = p = instance
        self.fixed_base = fixed_base
        digits, top = [], {}
        for f in p.forms:
            carry = 0
            col = []
            for i in range(p.blocks):
                v = (f[i] if i < len(f) else 0) + carry
                if fixed_base is None:
                    col.append(v)
                    carry = -int(v < 0)
                else:
                    carry, digit = divmod(v, fixed_base)
                    col.append(digit)
            top[f] = (f[p.blocks] if len(f) > p.blocks else 0) + carry
            digits.append(tuple(col))
        self.top = top
        self.guesses = 1 << (p.blocks - 1)
        self.shifts = tuple(f for f in p.lags if f and top[f] == 0)
        self.initial = (tuple(digits), p.start, ((0, 0),) * len(p.comparisons),
                        tuple(tuple((guess << 1, p.start) for guess in range(self.guesses))
                              for _ in self.shifts))

    def step(self, state, name, symbol):
        p = self.p
        digits, row, comps, shifts = state
        cols = [sum((v & 1) << i for i, v in enumerate(d)) for d in digits]
        new_digits = tuple(tuple(v // 2 for v in d) for d in digits)
        new_comps = []
        for f, (less, diff) in zip(p.comparisons, comps):
            col = cols[p.index[f]]
            changed = symbol ^ col
            new_comps.append(((less & ~changed) | (col & changed), diff | changed))
        matrices = p.layers[name]
        new_shifts = []
        for f, options in zip(self.shifts, shifts):
            col = cols[p.index[f]]
            new_options = []
            for borrow, vector in options:
                emitted = symbol ^ col ^ borrow
                nxt = ((~symbol & (col | borrow)) | (col & borrow)) & p.mask
                new_options.append((nxt, row_times(vector, matrices[emitted])))
            new_shifts.append(tuple(new_options))
        return new_digits, row_times(row, matrices[symbol]), tuple(new_comps), tuple(new_shifts)

    def observations(self, state):
        p = self.p
        _, row, comps, shifts = state
        cmp = {}
        for f, (less, diff) in zip(p.comparisons, comps):
            if self.top[f]:
                cmp[f] = -1 if self.top[f] > 0 else 1
            elif diff:
                cmp[f] = -1 if less & (1 << (diff.bit_length() - 1)) else 1
            else:
                cmp[f] = 0
        rows = {(): row}
        for f, options in zip(self.shifts, shifts):
            # Initial carry in digit i+1 must equal final borrow from digit i.
            valid = [(b, v) for guess, (b, v) in enumerate(options)
                     if (b & (self.guesses - 1)) == guess]
            assert len(valid) == 1
            borrow, vector = valid[0]
            if borrow < self.guesses:
                rows[f] = vector

        return cmp, rows

    def violation(self, state):
        p = self.p
        cmp, rows = self.observations(state)

        def predecessor(g, lag):
            if lag in rows:
                return p.read_pins(g, rows[lag])
            bit = int(any(cmp[point] == 0 for point in p.seed_points[g, lag]))
            return (1 - bit, bit)

        return p.check_pins(cmp[p.horizon], lambda g: p.read_pins(g, rows[()]), predecessor,
                            lambda g, lag: (g, lag if self.fixed_base is None else polynomial(lag, self.fixed_base)))

    def advance(self, frontier, layers):
        for name in layers:
            nxt = {}
            for state, word in frontier.items():
                for symbol in range(self.p.mask + 1):
                    target = self.step(state, name, symbol)
                    if target not in nxt:
                        nxt[target] = word + (symbol,)
            frontier = nxt
        return frontier


def decode(word, blocks):
    return sum(((symbol >> i) & 1) << (i * len(word) + j)
               for j, symbol in enumerate(word) for i in range(blocks))


def check(data):
    p = Instance(data)
    repeats = 0
    while True:
        schedule = p.prefix + p.loop * repeats + p.suffix
        h = len(schedule)
        geometry = p.geometry(h)
        if geometry:
            return {"valid": False, "h": h, "repetitions": repeats, "geometry": geometry}
        if h >= p.safe_h:
            break
        machine = Folded(p, fixed_base=1 << h)
        for state, word in machine.advance({machine.initial: ()}, schedule).items():
            defect = machine.violation(state)
            if defect:
                u = decode(word, p.blocks)
                assert defect == p.scalar_at(schedule, u)
                return {"valid": False, "h": h, "repetitions": repeats, "time": u,
                        "gate": defect[0], "reason": defect[1]}
        repeats += 1

    machine = Folded(p)
    frontier = machine.advance({machine.initial: ()}, p.prefix + p.loop * repeats)
    seen = set(frontier)
    first_tail = repeats
    while frontier:
        for state, word in machine.advance(frontier, p.suffix).items():
            defect = machine.violation(state)
            if defect:
                u = decode(word, p.blocks)
                # Every reported tail witness is also independently checked using raw integers.
                assert defect == p.scalar_at(p.prefix + repeats * p.loop + p.suffix, u)
                return {"valid": False, "h": len(word), "repetitions": repeats,
                        "time": u, "gate": defect[0], "reason": defect[1]}
        candidates = machine.advance(frontier, p.loop)
        frontier = {s: w for s, w in candidates.items() if s not in seen}
        seen.update(frontier)
        repeats += 1
    return {"valid": True, "finite_prefix_lengths": first_tail,
            "reachable_loop_boundary_states": len(seen)}


def example():
    # At t=B-1 the negative one-seed overrides the ordinary startup zeros.
    # Coordinates encode constant 1, high digit zero, and (high zero, low all ones).
    matrices = [[1, 2 if s < 2 else 0, 4 if s == 1 else 0] for s in range(4)]
    return {"blocks": 2, "width": 3, "start": 7, "layers": {"a": matrices},
            "prefix": ["a"], "loop": ["a"], "suffix": ["a"], "gates": [
                {"name": "unit", "inputs": [], "table": "1", "seeds": [-1], "pins": [0, 1]},
                {"name": "delay", "inputs": [["unit", 0, 1]], "table": "01", "pins": [6, 7]},
                {"name": "neg", "inputs": [["delay", 0, 0]], "table": "10", "pins": [7, 6]},
                {"name": "shared", "inputs": [["neg", -1, 1], ["neg", -1, 1]],
                 "table": "0110", "pins": [1, 0]}],
            "last_gate": "neg", "terminal": {"gate": "neg", "value": 0, "horizon": [1, 1]}}


def self_test():
    e = example()
    assert check(e)["valid"]
    e["gates"][0]["seeds"] = []
    assert not check(e)["valid"]
    e = example()
    e["gates"][2]["pins"] = [0, 0]
    e["terminal"]["gate"] = e["last_gate"] = "shared"
    assert check(e)["valid"]  # shared XOR still works with a completely unpinned source
    e["terminal"]["value"] = 1
    assert check(e)["reason"] == "terminal pin missing"

    rng = random.Random(1979)
    total = 0
    for blocks in (1, 2, 3):
        for seed in range(3):
            e = example()
            e.update(blocks=blocks, layers={label: [[rng.randrange(8) for _ in range(3)]
                                                     for _ in range(1 << blocks)] for label in "ab"})
            e["prefix"], e["loop"], e["suffix"] = ["a"], ["b", "a"], ["b"]
            e["terminal"]["horizon"] = ([-1, 1] if blocks == 1 else [-1, 2])
            if seed:
                e["gates"][0]["pins"] = [0, 0]
                e["gates"][1]["pins"] = [rng.randrange(8), rng.randrange(8)]
                e["gates"][0]["seeds"] = [-1, -3]
            p = Instance(e)
            machine = Folded(p)
            h = p.safe_h + seed
            schedule = tuple("ab"[j % 2] for j in range(h))
            assert p.geometry(h) is None
            for u in range(min(1 << (blocks * h), 80)):
                state = machine.initial
                for j, layer in enumerate(schedule):
                    col = sum(((u >> (h * i + j)) & 1) << i for i in range(blocks))
                    state = machine.step(state, layer, col)
                assert machine.violation(state) == p.scalar_at(schedule, u)
                total += 1

    # Check all shift rows, underflow bits and seed/horizon comparisons even
    # when the first failing gate would otherwise hide an arithmetic defect.
    arithmetic = 0
    for blocks in (1, 2, 3):
        e = example()
        e["blocks"] = blocks
        e["layers"] = {"a": [[rng.randrange(8) for _ in range(3)] for _ in range(1 << blocks)]}
        e["terminal"]["horizon"] = [-1] + [0] * (blocks - 1) + [1]
        e["gates"][0]["seeds"] = [-1, -11]
        for c, d in [(-3, 1), (3, 0), (11, 0), (3, 2), (0, 7), (-11, 4)]:
            e["gates"].append({"name": "test%s_%s" % (c, d), "table": "01",
                               "inputs": [["unit", c, d]], "pins": [0, 0]})
        p = Instance(e)
        for h in (2, 3, p.safe_h, p.safe_h + 1):
            base = 1 << h
            schedule = ("a",) * h
            for uniform in (False, True) if h >= p.safe_h else (False,):
                machine = Folded(p, None if uniform else base)
                times = {0, base ** blocks - 1, *(rng.randrange(base ** blocks) for _ in range(40))}
                for f in p.forms:
                    n = polynomial(f, base)
                    times.update(u for u in (n - 1, n, n + 1) if 0 <= u < base ** blocks)
                for u in times:
                    state = machine.initial
                    word = []
                    for j in range(h):
                        col = sum(((u >> (h * i + j)) & 1) << i for i in range(blocks))
                        word.append(col)
                        state = machine.step(state, "a", col)
                    assert decode(word, blocks) == u
                    cmp, rows = machine.observations(state)
                    for f in p.comparisons:
                        n = polynomial(f, base)
                        assert cmp[f] == (u > n) - (u < n)
                        arithmetic += 1
                    for f in p.lags:
                        n = u - polynomial(f, base)
                        assert rows.get(f) == (p.read_row(n, schedule) if n >= 0 else None)
                        arithmetic += 1

    # Distinct signed lag forms coincide only at the first included width.
    # That width must group both unknown parents in the XOR, before checking
    # without aliases at the larger widths (where the asserted pin fails).
    e = example()
    e["gates"] = [dict(name="q", inputs=[], table="0", pins=[0, 0]),
                  dict(name="x", inputs=[["q", 4, 0], ["q", 0, 1]], table="0110", pins=[1, 0])]
    e["terminal"] = dict(gate="x", value=0, horizon=[0, 1])
    del e["last_gate"]
    result = check(e)
    assert not result["valid"] and result["h"] == 3

    # A length-dependent WFA has its first missing terminal on a tail width.
    e = {"blocks": 1, "width": 5, "start": 1,
         "layers": {"cycle": [[2, 4, 8, 16, 1]] * 2}, "prefix": [],
         "loop": ["cycle"], "suffix": [],
         "gates": [{"name": "z", "inputs": [], "table": "0", "pins": [15, 0]}],
         "terminal": {"gate": "z", "value": 0, "horizon": []}}
    result = check(e)
    assert not result["valid"] and result["h"] == 4 and result["time"] == 0
    print("PASS: all-width certificates, failure/alias controls, "
          "%d direct semantic and %d direct arithmetic comparisons" % (total, arithmetic))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--example", action="store_true")
    group.add_argument("--self-test", action="store_true")
    group.add_argument("instance", nargs="?")
    args = parser.parse_args()
    if args.example:
        print(json.dumps(example(), indent=2))
    elif args.self_test:
        self_test()
    else:
        with (sys.stdin if args.instance == "-" else open(args.instance)) as file:
            result = check(json.load(file))
        print(json.dumps(result))
        sys.exit(0 if result["valid"] else 1)
