"""Audit the bit projection from list non-distinctness to two permutations and a packing.

PicoSAT checks the physical three-incidence equations on all or selected lists per shape.
All audited shapes exhaust every list and verify all output coordinates and holes.
"""

from itertools import product

import pycosat

from signed_permutation_cover_audit import (
    base_weights, compile_positive, coverage, guard, inverse, literal_value, patch,
)
from two_permutation_sat_audit import compile_source


def duplicate_cnf(rows, width, constant_mask):
    """Compile choose-at-least-two + equal-to-consensus, independently of the input bits."""
    n = rows * width
    data = list(range(1, n + 1))

    def fresh():
        nonlocal n
        n += 1
        return n

    companions = [fresh() for _ in data] if constant_mask else []
    consensus = [fresh() for _ in range(width)]
    choose = [fresh() for _ in range(rows)]
    clauses = []
    for i, bit in enumerate(data):
        selected = choose[i // width]
        target = consensus[i % width]
        clauses.extend([(-selected, -bit, target), (-selected, bit, -target)])

    for bit, other in zip(data, companions):
        clauses.extend([(bit, other), (-bit, -other)])
    gates = []
    seen, pair = fresh(), fresh()
    clauses.extend([(-seen,), (-pair,)])

    def gate(op, a, b):
        c = fresh()
        if op == 'or':
            clauses.extend([(-a, c), (-b, c), (a, b, -c)])
        else:
            clauses.extend([(a, -c), (b, -c), (-a, -b, c)])
        gates.append((op, a, b, c))
        return c

    for selected in choose:
        same = gate('and', seen, selected)
        seen = gate('or', seen, selected)
        pair = gate('or', pair, same)
    clauses.append((pair,))
    assert all(len({abs(v) for v in row if abs(v) in data}) <= 1 for row in clauses)
    return data, companions, choose, consensus, gates, clauses


# In a raw patch, the Q-incidences at columns 5 and 4 receive the external rails.
RAW_P = [2, 0, 4, 5, 3, 1]
RAW_Q = [1, 5, 3, 0, 2, 4]


def check_open_patch():
    for bit in (0, 1):
        p = RAW_P.copy()
        if bit:
            p[1], p[2] = p[2], p[1]
        for x, y in product(range(2), repeat=2):
            accepted = []
            for h in product(range(2), repeat=6):
                row = coverage(p, RAW_Q, h)
                row[RAW_Q[5]] += x - h[5]
                row[RAW_Q[4]] += y - h[4]
                if row == [1]*6:
                    assert (x, y) == (h[5], h[4])
                    accepted.append({i for i, z in enumerate(h) if z})
            expected = []
            if (x, y) == (0, 0):
                expected = [{1, 2}]
            elif (x, y) == (bit, 1 - bit):
                expected = [{2, 5} if bit else {1, 4}]
            assert accepted == expected


class Shape:
    def __init__(self, rows, width, constant_mask):
        self.width = width
        self.data, self.companions, self.choose, self.consensus, self.gates, cnf = duplicate_cnf(
            rows, width, constant_mask)
        self.g, self.guards, self.cnf = guard(cnf)
        self.zero = {i: 0 for i in range(1, self.g + 1)}
        triples, _ = self.weights(self.zero)
        pb, qb, self.labels, self.names = compile_source(triples)
        representative = {}
        for i, name in enumerate(self.names):
            representative.setdefault(name, self.labels['x', i])
        hp, hq, h, solutions = patch()
        self.tail = list(solutions[0])
        signed = {'D': -1, 'H0': 1, 'H1': 1, 'H2': 1, 'Z0': 0, 'Z1': 0}
        self.signed_tail = [0] * 6
        for wire, label in h.items():
            self.signed_tail[label] = signed[wire]
        self.forward_p, self.forward_q = inverse(pb), inverse(qb)
        self.switches = []
        hp, hq = inverse(hp), inverse(hq)
        self.constant_mask = constant_mask
        for i, v in enumerate(self.data):
            offset = len(self.forward_p)
            component_p, component_q = (RAW_P, RAW_Q) if constant_mask else (hp, hq)
            self.forward_p.extend(offset + j for j in component_p)
            self.forward_q.extend(offset + j for j in component_q)
            if constant_mask:
                for core, port in [(v, 5), (self.companions[i], 4)]:
                    a, b = representative['base', core], offset + port
                    self.forward_q[a], self.forward_q[b] = self.forward_q[b], self.forward_q[a]
                self.switches.append([offset + 1, offset + 2])
            else:
                self.switches.append([offset + h['H0'], representative['base', v],
                                      representative['neg', v]])

        offset = len(self.forward_p)
        self.forward_p.extend(offset + j for j in hp)
        self.forward_q.extend(offset + j for j in hq)
        self.guard_d = offset + h['D']
        a, b = offset + h['H0'], representative['neg', self.g]
        self.forward_p[a], self.forward_p[b] = self.forward_p[b], self.forward_p[a]
        self.qb = inverse(self.forward_q)
        touched = [v for group in self.switches for v in group]
        assert len(touched) == len(set(touched))

        # Rename the two internal switch images to an aligned pair, or the three
        # selectable images of the original one-port variant to an aligned block.
        self.rename = [None] * len(self.forward_p)
        used = set()
        stride = 2 if constant_mask else 4
        for i, group in enumerate(self.switches):
            for j, port in enumerate(group):
                target = stride*i + j
                self.rename[self.forward_p[port]] = target
                used.add(target)
        free = (v for v in range(len(self.forward_p)) if v not in used)
        for i in range(len(self.rename)):
            if self.rename[i] is None:
                self.rename[i] = next(free)
        self.order = inverse(self.rename)

    def weights(self, values):
        assignment = values.copy()
        for h, a in self.guards:
            assignment[h] = assignment[self.g] * (1 - literal_value(assignment, a))
        return compile_positive(self.g, self.cnf, assignment)

    def switched_arrays(self, bits):
        p = self.forward_p.copy()
        for group, bit in zip(self.switches, bits):
            if self.constant_mask:
                if not bit:
                    continue
                a, b = group
            else:
                a, b = group[0], group[bit + 1]
            p[a], p[b] = p[b], p[a]
        qb = self.qb
        pb = inverse(p)
        assert all(len({u, pb[u], qb[u]}) == 3 for u in range(len(p)))
        return p, self.forward_q

    def witness(self, bits, matching=None):
        vals = self.zero.copy()
        if not self.companions or matching is not None:
            vals.update(zip(self.data, bits))
            vals.update(zip(self.companions, (1-bit for bit in bits)))
        if matching is not None:
            vals[self.g] = 1
            i, j = matching
            vals[self.choose[i]] = vals[self.choose[j]] = 1
            vals.update(zip(self.consensus, bits[i * self.width:(i + 1) * self.width]))
            for op, a, b, c in self.gates:
                vals[c] = (vals[a] | vals[b]) if op == 'or' else (vals[a] & vals[b])
        _, positive = self.weights(vals)
        selection = base_weights(self.labels, self.names, positive)
        for bit in bits:
            if self.constant_mask:
                chosen = {1, 2} if matching is None else ({2, 5} if bit else {1, 4})
                selection.extend(int(i in chosen) for i in range(6))
            else:
                selection.extend(self.tail)
        selection.extend(self.tail)
        if matching is None:
            assert selection[self.guard_d] == 1
            selection[self.guard_d] = 0
        return selection


def exact_cover_solve(p, q):
    pb, qb = inverse(p), inverse(q)
    def clauses():
        for i, (v, w) in enumerate(zip(pb, qb)):
            a, b, c = i + 1, v + 1, w + 1
            yield [a, b, c]
            yield [-a, -b]
            yield [-a, -c]
            yield [-b, -c]
    answer = pycosat.solve(clauses())
    assert answer == 'UNSAT' or isinstance(answer, list)
    return answer != 'UNSAT'


def signature(shape, p, q, packing):
    # Zero-padding each word to a fixed whole number of bytes preserves projections.
    width = max(1, ((len(p) - 1).bit_length() + 7) // 8)
    raw = b''.join(shape.rename[perm[j]].to_bytes(width, 'little')
                   for perm in (p, q) for j in shape.order)
    return int.from_bytes(raw + bytes(packing[j] for j in shape.order), 'little')


def audit(m, b, solve, constant_mask=True):
    shape = Shape(m, b, constant_mask)
    n = m * b
    word_bytes = max(1, ((len(shape.forward_p) - 1).bit_length() + 7) // 8)
    array_bits = 8 * word_bytes * len(shape.forward_p)
    perm_mask = (1 << array_bits) - 1
    deltas = []
    influenced = 0
    positives = 0
    for data in range(1 << n):
        bits = [(data >> j) & 1 for j in range(n)]
        p, q = shape.switched_arrays(bits)
        partial = shape.witness(bits)
        count = coverage(p, q, partial)
        assert count.count(0) == 3 and set(count) == {0, 1}
        signed = partial[:-6] + shape.signed_tail
        assert signed.count(-1) == 1 and coverage(p, q, signed) == [1] * len(p)
        words = [tuple(bits[j*b:(j+1)*b]) for j in range(m)]
        matching = next(((i, j) for i in range(m) for j in range(i) if words[i] == words[j]), None)
        if matching is not None:
            assert coverage(p, q, shape.witness(bits, matching)) == [1] * len(p)
            positives += 1
        if data in solve:
            assert exact_cover_solve(p, q) == (matching is not None)

        out = signature(shape, p, q, partial)
        if data == 0:
            reference = out
        elif data.bit_count() == 1:
            changed = out ^ reference
            assert (changed & perm_mask).bit_count() == (2 if constant_mask else 4)
            assert (changed >> array_bits) & perm_mask == 0
            assert (changed >> (2 * array_bits)).bit_count() == (0 if constant_mask else 90)
            assert changed & influenced == 0
            influenced |= changed
            deltas.append(changed)
        expected = reference
        for j in range(data.bit_length()):
            if bits[j]:
                expected ^= deltas[j]
        assert expected == out
    mode = 'fixed masks' if constant_mask else 'varying masks'
    print(f'{m} x {b} ({mode}): q={len(p)}, {1<<n} lists, {positives} explicit exact covers, '
          f'{influenced.bit_count()} unary-dependent physical bits, '
          f'{len(solve)} physical decision checks', flush=True)


if __name__ == '__main__':
    check_open_patch()
    audit(2, 1, range(4), constant_mask=False)
    audit(2, 1, range(4))
    audit(2, 2, (0, 4))
    audit(3, 2, (0, 36))
