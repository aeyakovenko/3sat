"""Finite native-site calibration with endogenous SAT replies.

Every site executes the same heuristic on the actual bytes of each query.
The query circuit encodes that same heuristic's particular behavior on this
compiler's legal files. The first clause is always true but its first sign
varies with the request. This permits finite self-description without a
recursive compiler call or externally supplied solver-answer bits.
"""

from functools import lru_cache
from itertools import product

from cnf_width_dictionary_audit import read_dimacs
from shared_horn_sat_block_audit import (
    START, READ0, READ1, QUIET, RETURN, LEFT, RIGHT, SITES,
    code_bits, execute, obligations, satisfies,
)


def tag_sign(prefix, omitted, layout):
    if not prefix and not omitted:
        return True
    index = 1
    for bit in prefix:
        index = 2 * index + bit
    key = (index * 11 + omitted) * (37 + 2 * layout) + 13 * layout
    return key.bit_count() % 2 == 0


def candidate_solver(raw):
    # These files have no comments or whitespace between the header
    # newline and the first signed literal of the first clause.
    return raw[raw.index(b"\n") + 1] != ord("-")


class Circuit:
    def __init__(self, tag):
        self.count = 4
        self.one = 4
        self.rows = [(1 if tag else -1, 4, 2)]
        for pattern in range(1, 8):
            self.rows.append(tuple(-i if pattern >> (i - 1) & 1 else i for i in (1, 2, 3)))
        self.add(4)
        self.ors = {}

    def fresh(self):
        self.count += 1
        return self.count

    def add(self, *lits):
        row = list(dict.fromkeys(lits))
        if any(-x in row for x in row):
            return
        used = {abs(x) for x in row}
        pads = [x for x in (1, 2, 3) if x not in used]
        assert len(row) <= 3
        self.rows.append(tuple(row + pads[:3 - len(row)]))

    def either(self, left, right):
        key = tuple(sorted((left, right)))
        if key not in self.ors:
            gate = self.fresh()
            self.add(-left, gate)
            self.add(-right, gate)
            self.add(-gate, left, right)
            self.ors[key] = gate
        return self.ors[key]

    def both(self, left, right):
        return -self.either(-left, -right)

    def lookup(self, bits, leaves):
        # Binary multiplexers consume the bits in most-significant-first order.
        level = list(leaves)
        for bit in reversed(bits):
            level = [self.either(self.both(-bit, z), self.both(bit, o))
                     for z, o in zip(level[::2], level[1::2])]
        assert len(level) == 1
        return level[0]

    def literal(self, value):
        return self.one if value else -self.one

    def bytes(self):
        body = [f"p cnf {self.count} {len(self.rows)}"]
        body.extend(f"{a} {b} {c} 0" for a, b, c in self.rows)
        return ("\n".join(body) + "\n").encode()


def symbolic_runs(net, layout):
    # A receipt for a future file equals its computed first-clause sign.
    # Build the adaptive prefix and omission logic. The y below is the
    # program's computed y, distinct from the SAT witness's candidate site.
    chosen = []
    for i in range(3):
        leaves = [net.literal(tag_sign(p + (False,), 0, layout))
                  for p in product((False, True), repeat=i)]
        chosen.append(-net.lookup(chosen, leaves))
    data = [None]
    for i in range(1, 8):
        leaves = [net.literal(tag_sign(code_bits(z), i, layout)) for z in range(8)]
        data.append(-net.lookup(chosen, leaves))
    selected_flag = -data[RETURN]
    permitted = net.lookup([selected_flag], [data[READ0], data[READ1]])
    slots = [-data[RETURN], data[START], net.either(-data[START], permitted),
             net.either(-data[READ0], data[QUIET]), net.either(-data[READ1], data[RETURN]),
             net.either(-data[LEFT], data[QUIET]), net.either(-data[RIGHT], data[QUIET])]
    exists = net.literal(tag_sign((), 0, layout))
    flags = [net.both(exists, net.lookup(chosen,
                          [slots[(z - y) % SITES] for y in range(SITES)] + [-net.one]))
             for z in range(SITES)]
    return flags, [exists, *(-b for b in chosen), *(-b for b in data[1:])]


@lru_cache(None)
def compile_query(layout, prefix=(), omitted=0):
    net = Circuit(tag_sign(prefix, omitted, layout))
    flags, _ = symbolic_runs(net, layout)
    # Witness site and a candidate short chart for its ACTUAL execution.
    site = [net.fresh() for _ in range(3)]
    chart = [None] + [net.fresh() for _ in range(7)]
    net.add(-site[0], -site[1], -site[2])
    outcome = net.lookup(site, flags + [-net.one])
    net.add(chart[START])
    net.add(-chart[RETURN])
    net.add(-chart[START], -outcome, chart[READ1])
    net.add(-chart[START], outcome, chart[READ0])
    for origin, dest in ((READ0, QUIET), (READ1, RETURN), (LEFT, QUIET), (RIGHT, QUIET)):
        net.add(-chart[origin], chart[dest])
    net.add(chart[LEFT], chart[RIGHT])
    net.add(-chart[LEFT], -chart[RIGHT])
    for var, bit in zip(site, prefix):
        net.add(var if bit else -var)
    if omitted:
        net.add(-chart[omitted])
    return net.bytes()


def run_site(z, layout):
    receipts = []

    def issue(prefix=(), omitted=0):
        raw = compile_query(layout, prefix, omitted)
        answer = candidate_solver(raw)
        receipts.append((prefix, omitted, answer))
        return answer

    if not issue():
        return False, tuple(receipts)
    prefix = ()
    for _ in range(3):
        prefix += (not issue(prefix + (False,)),)
    chosen = sum(int(x) << (2 - i) for i, x in enumerate(prefix))
    if chosen == 7:
        return False, tuple(receipts)
    table = tuple(not issue(prefix, i) for i in range(1, 8))
    return execute(z, chosen, table).returned, tuple(receipts)


@lru_cache(None)
def exact_sat(raw):
    # Independent DPLL on the emitted bytes. No circuit, tags, special
    # constants, or chart semantics are supplied to this solver.
    rows = [tuple(map(int, clause)) for clause in read_dimacs(raw)]
    assert all(len(clause) == len({abs(x) for x in clause}) == 3 for clause in rows)

    def search(bits):
        while True:
            before = len(bits)
            pivot = None
            for row in rows:
                if any(abs(x) in bits and bits[abs(x)] == (x > 0) for x in row):
                    continue
                free = [x for x in row if abs(x) not in bits]
                if not free:
                    return False
                if len(free) == 1:
                    bits[abs(free[0])] = free[0] > 0
                else:
                    possible = min(map(abs, free))
                    pivot = possible if pivot is None else min(pivot, possible)
            if len(bits) == before:
                break
        if pivot is None:
            return True
        return any(search(bits | {pivot: value}) for value in (False, True))

    return search({})


def flip_first_sign(raw):
    pos = raw.index(b"\n") + 1
    return raw[:pos] + (raw[pos + 1:] if raw[pos:pos + 1] == b"-" else b"-" + raw[pos:])


def check_trace_wires(layout, flags, receipts):
    net = Circuit(tag_sign((), 0, layout))
    encoded_flags, encoded_receipts = symbolic_runs(net, layout)
    wires = encoded_receipts + encoded_flags
    observed = [answer for _, _, answer in receipts] + list(flags)
    assert len(observed) == len(wires)
    original = net.rows.copy()
    for wire, bit in zip(wires, observed):
        net.rows = original.copy()
        net.add(-wire if bit else wire)
        assert not exact_sat(net.bytes())
    net.rows = original.copy()
    for wire, bit in zip(wires, observed):
        net.add(wire if bit else -wire)
    assert exact_sat(net.bytes())
    return len(wires)


def main():
    requests = [(p, 0) for k in range(4) for p in product((False, True), repeat=k)]
    requests.extend((code_bits(z), bit) for z in range(8) for bit in range(1, 8))
    total_calls = wrong_yes = wrong_no = flips = checked_wires = 0
    outcomes = set()
    observed_wrong = set()
    for layout in (0, 1, 2):
        runs = [run_site(z, layout) for z in range(SITES)]
        flags = tuple(ret for ret, _ in runs)
        assert any(flags) and not all(flags)
        outcomes.add(flags)
        receipts = runs[0][1]
        assert all(record == receipts for _, record in runs)
        checked_wires += check_trace_wires(layout, flags, receipts)
        total_calls += sum(len(record) for _, record in runs)
        # Independent ground truth: enumerate the actual seven traces and
        # all semantic chart tables, including short-format restrictions.
        honest = [(code_bits(z), table) for z in range(SITES)
                  for table in product((False, True), repeat=7)
                  if table[LEFT - 1] != table[RIGHT - 1] and satisfies(obligations(flags[z]), table)]
        for prefix, omitted in requests:
            raw = compile_query(layout, prefix, omitted)
            truth = exact_sat(raw)
            assert truth == any(code[:len(prefix)] == prefix and (not omitted or not table[omitted - 1])
                                for code, table in honest)
            answer = candidate_solver(raw)
            assert answer == tag_sign(prefix, omitted, layout)
            wrong_yes += answer and not truth
            wrong_no += not answer and truth
            if (prefix, omitted, answer) in receipts and answer != truth:
                observed_wrong.add((layout, prefix, omitted, answer))
            if (prefix, omitted, answer) in receipts:
                mutant = flip_first_sign(raw)
                assert exact_sat(mutant) == truth and candidate_solver(mutant) != answer
                flips += 1
        print(f"layout {layout}: return bits {''.join(str(int(x)) for x in flags)}, "
              f"{len(honest)} admissible short charts")
    assert len(outcomes) >= 2 and wrong_yes and wrong_no
    assert {item[-1] for item in observed_wrong} == {False, True}
    print(f"{total_calls} actual SAT calls across 21 runs; {len(requests) * 3} entire query files checked")
    print(f"{wrong_yes} false YES, {wrong_no} false NO; {len(observed_wrong)} different actually issued wrong answers")
    for wrong in (False, True):
        layout, prefix, omitted, _ = min(row for row in observed_wrong if row[-1] == wrong)
        spelling = "".join(str(int(b)) for b in prefix) or "empty"
        print(f"issued counterexample: layout={layout}, prefix={spelling}, omitted={omitted}, "
              f"candidate={int(wrong)}, SAT={int(not wrong)}")
    print(f"{flips} first-clause sign flips preserved full-file SAT and reversed the heuristic")
    print(f"{checked_wires} individual receipt/output wire flips were UNSAT; all three actual transcripts were SAT")


if __name__ == "__main__":
    main()
