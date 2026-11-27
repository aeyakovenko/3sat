"""Check paired weighted sums against planar sweeps and parsed proper 3-CNF."""
from itertools import combinations, product
from random import Random

from weighted_range_transcript_audit import Transcript, count_models, proper, render


def projected_sums(points, queries, axes, n):
    """Weighted dominance in zero, one or two coordinates (keys are integral)."""
    if not axes:
        return [sum(weight for _, weight in points)] * len(queries)
    if len(axes) == 1:
        a = axes[0]
        sums = [0] * (n + 1)
        for coords, weight in points:
            sums[coords[a]] += weight
        for i in range(1, len(sums)):
            sums[i] += sums[i - 1]
        return [sums[coords[a]] for coords in queries]

    a, b = axes
    ordered = sorted(points, key=lambda point: point[0][a])
    tree = [0] * (n + 2)
    pos = 0
    answers = [0] * len(queries)
    for j in sorted(range(len(queries)), key=lambda j: queries[j][a]):
        query = queries[j]
        while pos < len(ordered) and ordered[pos][0][a] <= query[a]:
            coords, weight = ordered[pos]
            i = coords[b] + 1
            while i < len(tree):
                tree[i] += weight
                i += i & -i
            pos += 1
        i = query[b] + 1
        while i:
            answers[j] += tree[i]
            i -= i & -i
    return answers


def projected_pairs(points, queries, maximum):
    sums = projected_sums(points, queries, (), maximum)
    for size, sign in ((1, -1), (2, 1)):
        for axes in combinations(range(3), size):
            marginal = projected_sums(points, queries, axes, maximum)
            sums = [s + sign * update for s, update in zip(sums, marginal)]
    return sums


def direct(points, query):
    lower = sum(w for p, w in points if all(a <= b for a, b in zip(p, query)))
    upper = sum(w for p, w in points if all(a > b for a, b in zip(p, query)))
    return lower, upper


class PairedTranscript(Transcript):
    """Full-file format with a selectable query and two independent claim banks."""
    def __init__(self, n, schedule):
        self.bits = n.bit_length()
        self.radix = 1 << self.bits
        special = [
            [base + 12 + 10 * (v // 2) + v % 2 for v in range(self.radix)]
            for base in (0, 10 * self.radix)
        ]
        reserved = set(special[0] + special[1])
        self.last = max(reserved)
        self.false, self.true = 4, -4
        self.rows = [tuple(-i if mask & (1 << (i - 1)) else i for i in (1, 2, 3))
                     for mask in range(1, 8)]
        self.rows.extend(proper(-i) for i in range(4, self.last + 1) if i not in reserved)
        self.query = {j: self.fresh() for j, kind in enumerate(schedule) if kind == 'Q'}
        before = {}
        active = self.false
        for j in reversed(range(len(schedule))):
            if j in self.query:
                if active != self.false:
                    self.rows.append(proper(-active, -self.query[j]))
                active = self.or_gate(active, self.query[j])
            else:
                before[j] = active
        self.rows.append(proper(active))

        digits = [self.bit_word() for _ in range(6)]
        self.leaves = [self.decoder(digit) for digit in digits]
        for index, names in zip((2, 4), special):
            for actual, pinned in zip(self.leaves[index], names):
                self.rows.extend((proper(-actual, pinned), proper(actual, -pinned)))
            self.leaves[index] = names

        forward = digits[2] + digits[3] + [self.false]
        reverse = digits[4] + digits[5] + [self.false]
        claimed = self.add(forward, reverse)
        total = [self.false] * len(claimed)
        self.update = {}
        for j, earlier in before.items():
            x, y, weight = (self.bit_word() for _ in range(3))
            self.update[j] = (x, y, weight)
            x_ok = self.leq(x, digits[0])
            y_ok = self.leq(y, digits[1])
            down = self.and_gate(earlier, self.and_gate(x_ok, y_ok))
            up = self.and_gate(-earlier, self.and_gate(-x_ok, -y_ok))
            include = self.or_gate(down, up)
            term = [self.and_gate(include, wire) for wire in weight]
            total = self.add(total, term + [self.false] * (len(total) - len(term)))
        self.require_mismatch(total, claimed)
        self.positions = 3 * self.bits * len(before) + 3 * len(self.query)
        self.word_bytes = 96
        header = f"p cnf {self.last} {len(self.rows) + 2 * self.positions}\n".encode()
        raw = header + render(self.rows)
        self.prefix = raw + b" " * (-len(raw) % self.word_bytes)

    def add(self, left, right):
        carry = self.false
        result = []
        for a, b in zip(left, right):
            parity = self.xor_gate(a, b)
            result.append(self.xor_gate(parity, carry))
            carry = self.or_gate(self.and_gate(a, b), self.and_gate(parity, carry))
        return result

    def encode(self, records, order):
        assert len(records) == len(order) == self.positions
        blocks = []
        for i in order:
            kind, j, *args = records[i]
            if kind == 'U':
                field, bit, value = args
                wire = self.update[j][field][bit]
                rows = (proper(wire if value else -wire), (-1, 2, 3))
            else:
                if kind == 'Q':
                    bank, values = 0, args
                else:
                    assert kind in ('F', 'R')
                    bank = 2 if kind == 'F' else 4
                    values = (args[0] % self.radix, args[0] // self.radix)
                rows = [proper(-self.query[j], self.leaves[bank + k][v])
                        for k, v in enumerate(values)]
            raw = render(rows)
            assert len(raw) < self.word_bytes
            blocks.append(raw.ljust(self.word_bytes))
        return self.prefix + b''.join(blocks)


def main():
    rng = Random(9031)
    sweep_cases = 0
    for size in (4, 8, 16, 32):
        for _ in range(40):
            points = [(tuple(rng.randrange(size) for _ in range(3)), rng.randrange(1, 90))
                      for _ in range(size)]
            qs = [tuple(rng.randrange(size) for _ in range(3)) for _ in range(size)]
            assert projected_pairs(points, qs, size) == [sum(direct(points, q)) for q in qs]
            sweep_cases += size

    builder = PairedTranscript(4, 'UQUQ')
    points = [((0, 1, 2), 3), ((2, 4, 3), 4)]
    queries = [(1, 1, 2), (3, 4, 3)]
    true_words = [direct(points, q) for q in queries]
    assert true_words == [(3, 4), (7, 0)]
    order = list(range(builder.positions))
    rng.shuffle(order)
    count = twins = 0
    def make(forward, reverse):
        prefix = []
        for j, (coord, weight) in zip((0, 2), points):
            for k, value in enumerate((*coord[1:], weight)):
                for bit in range(builder.bits):
                    prefix.append(('U', j, k, bit, (value >> bit) & 1))
            index = j // 2
            prefix.extend((('Q', j + 1, *queries[index][1:]), ('F', j + 1, forward[index])))
        suffix = [('R', j, value) for j, value in zip((1, 3), reverse)]
        return builder.encode(prefix + suffix, order)

    for fs in product((2, 3, 4), (6, 7, 8)):
        for rs in product((3, 4, 5), (0, 1)):
            data = make(fs, rs)
            failures = sum(f + r != sum(pair) for f, r, pair in zip(fs, rs, true_words))
            assert count_models(data, builder.query.values()) == failures
            if rs == (4, 0):
                assert failures == sum(f != pair[0] for f, pair in zip(fs, true_words))
            count += 1
    original = make((3, 7), (4, 0))
    for other in (make((2, 7), (4, 0)), make((3, 7), (4, 1))):
        assert sum((a ^ b).bit_count() for a, b in zip(original, other)) == 1
        assert count_models(other, builder.query.values()) == 1
        twins += 1
    print(f"Passed {sweep_cases} projected sums, {count} parsed DIMACS counts, {twins} one-bit twins.")


if __name__ == '__main__':
    main()
