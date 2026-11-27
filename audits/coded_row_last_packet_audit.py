"""Check every possible one-packet replacement on small proper signed row-code files.

Uses PicoSAT when pycosat is installed, otherwise a bounded model-counting DPLL.
"""
from collections import Counter
from itertools import combinations, islice, product

from late_clause_replay_audit import Layout
from table_probe_context_audit import parse

try:
    import pycosat
except ImportError:
    pycosat = None


def dpll_count(clauses, unassigned, cap):
    while clauses:
        if any(not clause for clause in clauses):
            return 0
        lit = next((c[0] for c in clauses if len(c) == 1), None)
        if lit is None:
            pivot = min(clauses, key=len)[0]
            n = dpll_count(clauses + [(pivot,)], unassigned, cap)
            if n == cap:
                return n
            return n + dpll_count(clauses + [(-pivot,)], unassigned, cap-n)
        clauses = [tuple(x for x in c if x != -lit) for c in clauses if lit not in c]
        unassigned -= 1
    return min(cap, 1 << unassigned)


def model_count(raw, cap):
    clauses, bound = parse(raw)
    if pycosat is not None:
        return sum(1 for _ in islice(pycosat.itersolve(clauses, vars=bound), cap))
    return dpll_count(clauses, bound, cap)


class CodedRows:
    def __init__(self, a, matrix):
        assert a in (2, 4)
        self.a = a
        self.matrix = matrix
        self.h = len(matrix)
        self.q = len(matrix[0])
        assert all(len(row) == self.q for row in matrix)
        self.tags = [(12 + 10*j, 13 + 10*j) for j in range(self.q)]
        reserved = {v for flags in self.tags for v in flags}
        free = (i for i in range(1, 1000) if i not in reserved)
        selector = tuple(next(free) for _ in range((a-1).bit_length()))
        self.rows = tuple(next(free) for _ in range(a))
        self.bits = tuple(next(free) for _ in range(self.h))
        self.library = tuple(next(free) for _ in range(1 << a))
        gates = []

        def gate(inputs, out, value):
            for values in product((0, 1), repeat=len(inputs)):
                guard = tuple(-v if bit else v for v, bit in zip(inputs, values))
                gates.append(guard + (out if value(*values) else -out,))

        for i, row in enumerate(self.rows):
            gate(selector, row, lambda *v: sum(b << t for t, b in enumerate(v)) == i)
            for mask, name in enumerate(self.library):
                gates.append((-row, name if mask >> i & 1 else -name))
        for j, (negative, positive) in enumerate(self.tags):
            support = [self.bits[h] for h in range(self.h) if matrix[h][j]]
            if support:
                acc = support[0]
                for bit in support[1:]:
                    out = next(free)
                    gate((acc, bit), out, lambda x, y: x ^ y)
                    acc = out
                gate((acc,), positive, bool)
                gate((acc,), negative, lambda x: not x)
            else:
                gates.extend([(negative,), (-positive,)])
        used = {abs(v) for c in gates for v in c} | set(self.bits)
        bound = max(used)
        gates.extend([(-i,) for i in range(1, bound+1) if i not in used])
        self.layout = Layout(r=2, count=self.h*2, bits=1 << 16, variables=bound)
        anchors = self.layout.anchors
        guards = [tuple(-v if pattern & (1 << j) else v for j, v in enumerate(anchors))
                  for pattern in range(1, 8)]
        fixed = guards + [self.pad(c) for c in gates]
        header = f'p cnf {anchors[-1]} {len(fixed)+4*self.h}\n'.encode()
        public = header + b''.join(self.layout.record(c) for c in fixed)
        width = self.layout.word_bytes
        self.prefix = public + b' ' * (-len(public) % width)

    def pad(self, c):
        return c + self.layout.anchors[:3-len(c)]

    def packet_bytes(self, clauses):
        return self.layout.packet(clauses).to_bytes(self.layout.word_bytes, 'little')

    def data(self, h, mask):
        y, s = self.bits[h], self.library[mask]
        return self.packet_bytes([self.pad((-y, s)), self.pad((y, -s))])

    def query(self, i, j, e):
        return self.packet_bytes([self.pad((self.rows[i],)), self.pad((self.tags[j][e],))])

    def file(self, words):
        assert len(words) == self.layout.count and all(len(w) == self.layout.word_bytes for w in words)
        raw = self.prefix + b''.join(words)
        assert len(raw)*8 <= self.layout.bits
        return raw.ljust(self.layout.bits//8)


def audit(a, matrix, masks_cases):
    model = CodedRows(a, matrix)
    h, q = model.h, model.q
    masters = pairs = decoded = 0
    for masks in masks_cases:
        data = [model.data(col, mask) for col, mask in enumerate(masks)]
        master = data + data
        # Each row selector extends uniquely. The second occurrence is a real copy.
        assert model_count(model.file(master), a+1) == a
        masters += 1
        packed = [0]*q
        for t in range(h):
            for j, take in enumerate(matrix[t]):
                if take:
                    packed[j] ^= masks[t]
        for i, j in product(range(a), range(q)):
            bit = sum(((masks[t] >> i) & 1) * matrix[t][j] for t in range(h)) % 2
            assert ((packed[j] >> i) & 1) == bit
            decoded += 1
            queries = [model.query(i, j, e) for e in (0, 1)]
            offsets = [p for p, (u, v) in enumerate(zip(*queries)) if u != v]
            off, = offsets
            assert (queries[0][off], queries[1][off]) == (ord('2'), ord('3'))
            for slot in range(2*h):
                counts = []
                for packet in queries:
                    words = master.copy()
                    words[slot] = packet
                    counts.append(model_count(model.file(words), 2))
                assert counts == [int(bit == 0), int(bit == 1)]
                pairs += 1
    return masters, pairs, decoded


def binary_outputs(row, matrix):
    return sum((sum(((row >> k) & 1) * matrix[k][j] for k in range(len(matrix))) % 2) << j
               for j in range(len(matrix[0])))


def audit_affine_rectangles():
    # The top-left generator rectangle in both new maps deliberately differs
    # from its old value. Only the old directions on the free coordinates
    # must cover the old output space.
    cases = [
        (1, ((1, 0), (0, 1)), 2,
         ((0, 1, 1), (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 0))),
        (2, ((1, 1),), 3, ((0, 1, 0), (1, 0, 1), (0, 1, 1), (1, 0, 0))),
        (2, ((1, 0), (1, 1)), 3, ((0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 0, 0))),
    ]
    new_inputs = rectangles = old_instances = 0
    for a0, old, a1, new in cases:
        d0, m0, d1 = len(old), len(old[0]), len(new)
        assert tuple(row[:m0] for row in new[:d0]) != old
        old_bits, old_outputs = (1 << d0)-1, (1 << m0)-1
        reachable = {binary_outputs(y << d0, new) & old_outputs for y in range(1 << (d1-d0))}
        assert len(reachable) == 1 << m0
        targets = Counter()
        for rows in product(range(1 << d1), repeat=a1):
            original = tuple(x & old_bits for x in rows[:a0])
            answers = tuple(binary_outputs(x, new) & old_outputs for x in rows[:a0])
            targets[original, answers] += 1
            new_inputs += 1
        expected = 1 << (a1*d1 - a0*(d0+m0))
        assert len(targets) == 1 << (a0*(d0+m0))
        assert set(targets.values()) == {expected}
        rectangles += len(targets)
        for original in product(range(1 << d0), repeat=a0):
            signed_answers = tuple(binary_outputs(x, old) for x in original)
            assert targets[original, signed_answers] == expected
            old_instances += 1
    return new_inputs, rectangles, old_instances


def audit_query_batches():
    matrices = [
        (((1, 1), (1, 0)), list(product(range(4), repeat=2))),
        (((0, 1), (0, 1), (0, 1)), [(0, 0, 0), (1, 2, 3)]),
    ]
    batches = accepted = 0
    for matrix, cases in matrices:
        model = CodedRows(2, matrix)
        data_decode = [{model.data(k, mask): mask for mask in range(4)} for k in range(model.h)]
        query_decode = {model.query(i, j, e): (i, j, e) for i, j, e in
                        product(range(model.a), range(model.q), (0, 1))}
        # The public circuit uses one XOR chain for each of these supports.
        supports = [[h for h in range(model.h) if matrix[h][j]] for j in range(model.q)]

        def packed_decision(words):
            assertions = []
            masks = []
            for h in range(model.h):
                supplied = []
                for word in (words[h], words[model.h+h]):
                    if word in data_decode[h]:
                        supplied.append(data_decode[h][word])
                    else:
                        assertions.append(query_decode[word])
                assert supplied and len(set(supplied)) == 1
                masks.append(supplied[0])
            result = [0] * model.q
            for j, inputs in enumerate(supports):
                for h in inputs:
                    result[j] ^= masks[h]
            assert len({i for i, j, e in assertions}) == 1
            return all((result[j] >> i & 1) == e for i, j, e in assertions)

        for masks in cases:
            data = [model.data(k, z) for k, z in enumerate(masks)]
            for count in range(2, model.h+1):
                for cols in combinations(range(model.h), count):
                    for copies in product((0, 1), repeat=count):
                        slots = tuple(h + c*model.h for h, c in zip(cols, copies))
                        for i in range(model.a):
                            row = sum(((z >> i) & 1) << h for h, z in enumerate(masks))
                            reference = binary_outputs(row, matrix)
                            choices = tuple(product(range(model.q), (0, 1)))
                            for packet_ids in product(choices, repeat=count):
                                words = data + data
                                for slot, (j, e) in zip(slots, packet_ids):
                                    words[slot] = model.query(i, j, e)
                                gold = all((reference >> j & 1) == e for j, e in packet_ids)
                                assert packed_decision(words) == gold
                                assert model_count(model.file(words), 2) == int(gold)
                                batches += 1
                                accepted += gold
    return batches, accepted


def main():
    samples = [
        (2, ((0, 1),), product(range(4), repeat=1)),
        (2, ((1, 1, 0), (1, 0, 1)), product(range(4), repeat=2)),
        (2, ((1, 0), (1, 0), (1, 1)), [(0, 0, 0), (3, 2, 1), (1, 2, 3)]),
        (4, ((1, 0), (1, 0)), [(0, 0), (15, 15), (3, 12), (5, 9), (6, 11)]),
    ]
    results = [audit(a, matrix, cases) for a, matrix, cases in samples]
    masters, pairs, decoded = map(sum, zip(*results))
    print(f'{masters} all-data masters, {pairs} one-bit signed pairs in all marked '
          f'positions, {2*pairs} model counts on replacements, {decoded} packed row/column entries')
    inputs, rectangles, old = audit_affine_rectangles()
    print(f'{inputs} uniform extension candidates, {rectangles} prescribed rectangle '
          f'pairs, {old} old inputs with every signed output retained')
    batches, accepted = audit_query_batches()
    print(f'{batches} genuine multi-column replacement files and packed decisions, '
          f'{accepted} uniquely satisfiable')



if __name__ == '__main__':
    main()
