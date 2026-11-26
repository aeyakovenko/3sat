"""Count models of small word-aligned weighted-dominance transcript CNFs."""
from itertools import product
from random import Random

from table_probe_context_audit import parse


def proper(*row):
    literals = list(row)
    for anchor in (1, 2, 3):
        if len(literals) < 3 and anchor not in map(abs, literals):
            literals.append(anchor)
    assert len(literals) == len(set(map(abs, literals))) == 3
    return tuple(literals)


def render(rows):
    return b"".join((" ".join(map(str, row)) + " 0\n").encode() for row in rows)


class Transcript:
    rows_per_packet = 4

    def __init__(self, n, schedule):
        self.n = n
        self.bits = n.bit_length()
        self.radix = 1 << self.bits
        self.low_names = [12 + 10 * (v // 2) + v % 2 for v in range(self.radix)]
        self.last = max(self.low_names)
        self.false, self.true = 4, -4
        self.rows = [tuple(-i if mask & (1 << (i - 1)) else i for i in (1, 2, 3))
                     for mask in range(1, 8)]
        self.rows.extend(proper(-i) for i in range(4, self.last + 1)
                         if i not in self.low_names)
        self.query = {j: self.fresh() for j, kind in enumerate(schedule) if kind == 'Q'}
        self.before = {}
        active = self.false
        for j in reversed(range(len(schedule))):
            if schedule[j] == 'Q':
                if active != self.false:
                    self.rows.append(proper(-active, -self.query[j]))
                active = self.or_gate(active, self.query[j])
            else:
                self.before[j] = active
        self.rows.append(proper(active))
        coord_x, coord_y, answer_lo, answer_hi = (self.bit_word() for _ in range(4))
        self.leaves = [self.decoder(word) for word in (coord_x, coord_y, answer_lo, answer_hi)]
        for actual, special in zip(self.leaves[2], self.low_names):
            self.rows.extend((proper(-actual, special), proper(actual, -special)))
        self.leaves[2] = self.low_names
        self.update = {}
        total = [self.false] * (2*self.bits)
        for j, active in self.before.items():
            x, y, weight = (self.bit_word() for _ in range(3))
            self.update[j] = (x, y, weight)
            for wire in x + y + weight:
                self.rows.append(proper(active, -wire))
            include = self.and_gate(active, self.and_gate(self.leq(x, coord_x),
                                                        self.leq(y, coord_y)))
            term = [self.and_gate(include, wire) for wire in weight] + [self.false]*self.bits
            carry = self.false
            new_total = []
            for left, right in zip(total, term):
                mixed = self.xor_gate(left, right)
                new_total.append(self.xor_gate(mixed, carry))
                carry = self.or_gate(self.and_gate(left, right), self.and_gate(carry, mixed))
            total = new_total
        self.require_mismatch(total, answer_lo + answer_hi)
        positions = 3*self.bits*len(self.update) + 2*len(self.query)
        self.receipts = [self.fresh() for _ in range(positions)]
        received = self.false
        for receipt in self.receipts:
            received = self.or_gate(received, receipt)
        self.rows.append(proper(received))
        self.word_bytes = 160
        header = f"p cnf {self.last} {len(self.rows) + self.rows_per_packet*positions}\n".encode()
        raw = header + render(self.rows)
        self.prefix = raw + b" " * (-len(raw) % self.word_bytes)

    def require_mismatch(self, total, operand):
        mismatch = self.false
        for actual, claimed in zip(total, operand):
            mismatch = self.or_gate(mismatch, self.xor_gate(actual, claimed))
        self.rows.append(proper(mismatch))

    def fresh(self):
        self.last += 1
        return self.last

    def bit_word(self):
        return [self.fresh() for _ in range(self.bits)]

    def and_gate(self, a, b):
        if a == self.false or b == self.false or a == -b:
            return self.false
        if b == self.true or a == b:
            return a
        if a == self.true:
            return b
        c = self.fresh()
        self.rows.extend((proper(-a, -b, c), proper(a, -c), proper(b, -c)))
        return c

    def or_gate(self, a, b):
        return -self.and_gate(-a, -b)

    def xor_gate(self, a, b):
        if a == self.false:
            return b
        if b == self.false:
            return a
        if a == self.true:
            return -b
        if b == self.true:
            return -a
        if a == b:
            return self.false
        if a == -b:
            return self.true
        c = self.fresh()
        self.rows.extend((proper(a, b, -c), proper(-a, -b, -c),
                          proper(a, -b, c), proper(-a, b, c)))
        return c

    def decoder(self, word):
        layer = [self.true]
        for bit in reversed(word):
            layer = [self.and_gate(prefix, branch)
                     for prefix in layer for branch in (-bit, bit)]
        return layer

    def leq(self, x, y):
        result = self.true
        for a, b in zip(x, y):
            smaller = self.and_gate(-a, b)
            equal = -self.xor_gate(a, b)
            result = self.or_gate(smaller, self.and_gate(equal, result))
        return result

    def packet_rows(self, slot, rec):
        receipt = self.receipts[slot]
        kind, *fields = rec
        rows = [proper(-receipt)]
        if kind == 'Q':
            j, x, y = fields
            choice = self.query[j]
            rows = [proper(-receipt, choice), proper(receipt, -choice),
                    proper(-choice, self.leaves[0][x]), proper(-choice, self.leaves[1][y])]
        elif kind == 'A':
            j, answer = fields
            choice = self.query[j]
            rows.extend((proper(-choice, self.leaves[2][answer % self.radix]),
                         proper(-choice, self.leaves[3][answer // self.radix])))
        elif kind == 'U':
            j, field, bit, value = fields
            wire = self.update[j][field][bit]
            rows.append(proper(-self.before[j], wire if value else -wire))
        else:
            assert kind == 'D'
        return rows

    def packet(self, slot, rec):
        rows = self.packet_rows(slot, rec)
        assert len(rows) <= self.rows_per_packet
        rows.extend([(-1, 2, 3)] * (self.rows_per_packet-len(rows)))
        raw = render(rows)
        assert len(raw) < self.word_bytes
        return raw + b" " * (self.word_bytes-len(raw))

    def file(self, records, positions):
        slots = [('D',)] * len(positions)
        for index, rec in zip(positions, records):
            slots[index] = rec
        return self.prefix + b"".join(self.packet(i, rec) for i, rec in enumerate(slots))


def count_models(file, priority):
    clauses, count = parse(file)
    order = list(dict.fromkeys([1, 2, 3, *priority, *range(1, count+1)]))

    def visit(rows, assigned):
        while rows:
            if any(not row for row in rows):
                return 0
            forced = {row[0] for row in rows if len(row) == 1}
            if not forced:
                v = next(v for v in order if v not in assigned)
                return sum(visit([*rows, (literal,)], assigned) for literal in (v, -v))
            if any(-v in forced for v in forced):
                return 0
            assigned = assigned | {abs(v) for v in forced}
            rows = [tuple(v for v in row if -v not in forced)
                    for row in rows if not any(v in forced for v in row)]
        return 1 << (count-len(assigned))

    return visit(clauses, set())


def run():
    schedule = 'QUQUQ'
    builder = Transcript(3, schedule)
    updates = {1:(1, 2, 3), 3:(1, 2, 2)}
    queries = {0:(3, 3), 2:(1, 2), 4:(3, 3)}
    positions = list(range(len(builder.receipts)))
    rng = Random(2837)
    rng.shuffle(positions)
    cases = 0
    for choices in product((0, 1), repeat=3):
        records = []
        errors = 0
        for j, op in enumerate(schedule):
            if op == 'U':
                for field, val in enumerate(updates[j]):
                    records.extend(('U', j, field, bit, (val >> bit) & 1)
                                   for bit in range(builder.bits))
                continue
            x, y = queries[j]
            truth = sum(w for t, (a,b,w) in updates.items() if t < j and a<=x and b<=y)
            perturb = choices[len([old for old in queries if old < j])]
            records.extend((('Q', j, x, y), ('A', j, truth ^ perturb)))
            errors += perturb
            left = builder.file(records, positions)
            assert count_models(left, builder.query.values()) == errors
            other = builder.file([*records[:-1], ('A', j, truth ^ perturb ^ 1)], positions)
            assert sum((a^b).bit_count() for a, b in zip(left, other)) == 1
            assert count_models(other, builder.query.values()) == errors + (1 if not perturb else -1)
            cases += 2
    # Two nontrivial errors, a wrong high digit, and a query excluding both updates.
    alt = [('Q', 0, 1, 1), ('A', 0, 8)]
    for j in (1, 3):
        for field, val in enumerate(updates[j]):
            alt.extend(('U', j, field, bit, (val >> bit) & 1) for bit in range(builder.bits))
        alt.extend((('Q', j+1, 3, 1), ('A', j+1, 0 if j == 1 else 4)))
    assert count_models(builder.file(alt, positions), builder.query.values()) == 2
    # For n=4 the WY period is four. The last hard operation is an update.
    scheduled = Transcript(4, "QQQUQ")
    physical = list(reversed(range(len(scheduled.receipts))))
    prefix = []
    for j in range(3):
        prefix.extend((('Q', j, 1, 4), ('A', j, 0)))
    for field, val in enumerate((4, 1, 4)):
        prefix.extend(('U', 3, field, i, (val >> i) & 1) for i in range(scheduled.bits))
    prefix.append(('Q', 4, 4, 4))
    last = [scheduled.file([*prefix, ('A', 4, x)], physical) for x in (4,5)]
    assert [count_models(file, scheduled.query.values()) for file in last] == [0,1]
    assert sum((a^b).bit_count() for a, b in zip(*last)) == 1
    print(f"Checked {cases+3} parsed proper DIMACS files, including prefixes, model counts and one-bit replacements.")


if __name__ == '__main__':
    run()
