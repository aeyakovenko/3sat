"""Exact synthesis of a fixed opcode shape on a finite four-bit RAM path.

An accepting base path must give a different comparison transcript on every
rejecting input. Registers are in static single assignment form along that path.
The arithmetic circuit and the independent catalog interpreter implement the
same full primitive set used in exact-clocks-for-two-word-sat-inputs.md.
"""

from itertools import combinations, product

import numpy as np

ALU = ('and', 'or', 'xor', 'add', 'sub', 'mul', 'shl', 'shr', 'sar',
       'shlmod', 'shrmod', 'sarmod', 'rol', 'ror',
       'eq', 'lt', 'slt', 'ne', 'ge', 'sge')
BRANCH = ('eq', 'lt', 'slt')
BITS = range(4)


def words(code):
    return tuple((code >> shift) & 15 for shift in (12, 8, 4, 0))


def verdict(row):
    p, q, m, n = row
    return not ((p & m) or (q & n) or (m == n == 15))


def sensitive_base(code):
    vals = list(words(code))
    if not verdict(vals):
        return False
    for i in BITS:
        if not any(not verdict(vals[:i] + [v] + vals[i+1:]) for v in range(16)):
            return False
    return True


def shapes(depth):
    if depth < 5:
        return []
    forms = (''.join(p) + 'B' for p in product('LSBA', repeat=depth-1) if p.count('L') >= 4)
    return sorted(forms, key=lambda p: (p.count('A'), p.count('S'), p))


class Formula:
    def __init__(self):
        self.size = 1
        self.rows = [(1,)]
        self.gates = {}

    def variable(self):
        self.size += 1
        return self.size

    def word(self, val):
        return tuple(1 if val & (1 << k) else -1 for k in BITS)

    def both(self, a, b):
        if a == -1 or b == -1 or a == -b:
            return -1
        if a == 1 or a == b:
            return b
        if b == 1:
            return a
        key = ('and', min(a, b), max(a, b))
        if key not in self.gates:
            c = self.variable()
            self.rows.extend([(-c, a), (-c, b), (c, -a, -b)])
            self.gates[key] = c
        return self.gates[key]

    def either(self, a, b):
        return -self.both(-a, -b)

    def xor(self, a, b):
        if a == b:
            return -1
        if a == -b:
            return 1
        if abs(a) == 1:
            return -b if a == 1 else b
        if abs(b) == 1:
            return -a if b == 1 else a
        sign = 1 if a * b > 0 else -1
        a, b = sorted((abs(a), abs(b)))
        key = ('xor', a, b)
        if key not in self.gates:
            c = self.variable()
            self.rows.extend([(-a, -b, -c), (a, b, -c), (a, -b, c), (-a, b, c)])
            self.gates[key] = c
        return sign * self.gates[key]

    def mux(self, choice, yes, no):
        if yes == no:
            return yes
        return self.either(self.both(choice, yes), self.both(-choice, no))

    def all(self, literals):
        res = 1
        for lit in literals:
            res = self.both(res, lit)
        return res

    def any(self, literals):
        return -self.all(-lit for lit in literals)

    def choice(self, labels):
        if len(labels) == 1:
            return [(labels[0], 1)]
        choices = [(x, self.variable()) for x in labels]
        self.rows.append(tuple(v for _, v in choices))
        self.rows.extend((-a, -b) for (_, a), (_, b) in combinations(choices, 2))
        return choices

    def choose_word(self, options):
        return tuple(self.any(self.both(sel, value[j]) for sel, value in options) for j in BITS)

    def same(self, a, b):
        return self.all(-self.xor(u, v) for u, v in zip(a, b))

    def lt(self, a, b):
        less = -1
        for u, v in zip(a, b):
            less = self.mux(self.xor(u, v), v, less)
        return less

    def plus(self, a, b, carry=-1):
        res = []
        for u, v in zip(a, b):
            diff = self.xor(u, v)
            res.append(self.xor(diff, carry))
            carry = self.either(self.both(u, v), self.both(diff, carry))
        return tuple(res)

    def alu(self, name, a, b):
        if name in ('eq', 'ne', 'lt', 'ge', 'slt', 'sge'):
            if name in ('eq', 'ne'):
                result = self.same(a, b)
            elif name in ('slt', 'sge'):
                result = self.lt((*a[:3], -a[3]), (*b[:3], -b[3]))
            else:
                result = self.lt(a, b)
            if name in ('ne', 'ge', 'sge'):
                result = -result
            return (result, -1, -1, -1)
        if name in ('and', 'or', 'xor'):
            fn = {'and': self.both, 'or': self.either, 'xor': self.xor}[name]
            return tuple(fn(u, v) for u, v in zip(a, b))
        if name == 'add':
            return self.plus(a, b)
        if name == 'sub':
            return self.plus(a, tuple(-v for v in b), 1)
        if name == 'mul':
            out = self.word(0)
            for j in BITS:
                part = tuple(self.both(a[i-j], b[j]) if i >= j else -1 for i in BITS)
                out = self.plus(out, part)
            return out
        right = name in ('shr', 'sar', 'shrmod', 'sarmod', 'ror')
        rotate = name in ('rol', 'ror')
        fill = a[3] if name in ('sar', 'sarmod') else -1
        out = a
        for i in range(2):
            moved = []
            for j in BITS:
                src = j + (1 << i) if right else j - (1 << i)
                moved.append(out[src % 4] if rotate or 0 <= src < 4 else fill)
            out = tuple(self.mux(b[i], m, v) for m, v in zip(moved, out))
        if name in ('shl', 'shr', 'sar'):
            big = self.either(b[2], b[3])
            out = tuple(self.mux(big, fill, v) for v in out)
        return out


def operand(f, n_regs):
    return (f.choice([-1, *range(n_regs)]), tuple(f.variable() for _ in BITS))


def build(shape, base, negatives):
    if not sensitive_base(base):
        raise ValueError('base must be a sensitive positive on all four input words')
    if shape[-1] != 'B' or shape.count('L') < 4:
        raise ValueError('shape must have four loads and end in a comparison')
    if any(verdict(words(row)) for row in negatives):
        raise ValueError('opposite examples must be negative')
    f = Formula()
    instr = []
    n_regs = 0
    for action in shape:
        op = f.choice(ALU if action == 'A' else BRANCH) if action in 'AB' else []
        args = [operand(f, n_regs) for _ in range(1 if action == 'L' else 2)]
        instr.append((action, op, args))
        n_regs += action in 'LA'

    # With exactly four loads, each must read a distinct virgin input cell
    # on the sensitive base. Before any store or ALU, high base data words
    # cannot address one of these four cells. Consecutive such direct loads
    # can be reordered with their fresh register names permuted downstream.
    if shape.count('L') == 4 and min(words(base)) >= 4:
        previous = None
        for action, _, args in instr:
            if action in 'AS':
                break
            if action != 'L':
                previous = None
                continue
            opts, imm = args[0]
            f.rows.extend([(opts[0][1],), (-imm[2],), (-imm[3],)])
            if previous is not None:
                f.rows.append((f.lt(previous, imm),))
            previous = imm

    def evaluate(code, first):
        row = words(code)
        regs, stores, branch = [], [], []
        seen = [-1] * 4
        for action, op, args in instr:
            values = []
            for opts, imm in args:
                values.append(f.choose_word([(v, imm if j < 0 else regs[j]) for j, v in opts]))
            a = values[0]
            if action == 'L':
                at = [f.same(a, f.word(j)) for j in BITS]
                out = tuple(f.any(at[j] for j in BITS if row[j] & (1 << bit)) for bit in BITS)
                for address, value in stores:
                    selects = f.same(a, address)
                    out = tuple(f.mux(selects, u, v) for u, v in zip(value, out))
                regs.append(out)
                if first:
                    seen = [f.either(x, y) for x, y in zip(seen, at)]
            elif action == 'S':
                if first:
                    for j in BITS:
                        f.rows.append((-f.same(a, f.word(j)), seen[j]))
                stores.append(tuple(values))
            else:
                b = values[1]
                out = f.choose_word([(v, f.alu(name, a, b)) for name, v in op])
                if action == 'A':
                    regs.append(out)
                else:
                    branch.append(out[0])
        if first:
            f.rows.extend((v,) for v in seen)
        return branch

    base_branch = evaluate(base, True)
    for code in negatives:
        branch = evaluate(code, False)
        f.rows.append(tuple(f.xor(a, b) for a, b in zip(base_branch, branch)))
    return f, instr


def decode(instr, model):
    def chosen(opts):
        return next(key for key, selector in opts if selector in model)

    path = []
    for action, op, args in instr:
        operands = []
        for opts, imm in args:
            idx = chosen(opts)
            if idx < 0:
                operands.append(['i', sum(1 << j for j, v in enumerate(imm) if v in model)])
            else:
                operands.append(['r', idx])
        path.append([action, chosen(op) if op else None, *operands])
    return path


def primitive(name, a, b):
    """Independent ordinary integer operator, also supports NumPy int32 arrays."""
    sa, sb = (a ^ 8) - 8, (b ^ 8) - 8
    if name in ('eq', 'ne', 'lt', 'slt', 'ge', 'sge'):
        if name in ('eq', 'ne'):
            flag = a == b
        elif name in ('slt', 'sge'):
            flag = sa < sb
        else:
            flag = a < b
        return (flag ^ (name in ('ne', 'ge', 'sge'))) * 1
    if name == 'and':
        return a & b
    if name == 'or':
        return a | b
    if name == 'xor':
        return a ^ b
    if name == 'add':
        return (a + b) & 15
    if name == 'sub':
        return (a - b) & 15
    if name == 'mul':
        return (a * b) & 15
    sh = b & 3 if name.endswith('mod') or name in ('rol', 'ror') else b
    if name in ('shl', 'shlmod'):
        return (a << sh) & 15
    if name in ('shr', 'shrmod'):
        return a >> sh
    if name in ('sar', 'sarmod'):
        return (sa >> sh) & 15
    if name == 'rol':
        return ((a << sh) | (a >> (4-sh))) & 15
    if name == 'ror':
        return ((a >> sh) | (a << (4-sh))) & 15
    raise ValueError(name)


class Catalog:
    def __init__(self):
        codes = np.arange(65536, dtype=np.int32)
        self.original = [(codes >> sh) & 15 for sh in (12, 8, 4, 0)]
        p, q, m, n = self.original
        self.sat = ((p & m) == 0) & ((q & n) == 0) & ((m != 15) | (n != 15))

    def survivors(self, path, base):
        regs, stores = [], []
        agree = ~self.sat.copy()
        for action, op, *args in path:
            vals = [v if k == 'i' else regs[v] for k, v in args]
            a = vals[0]
            if action == 'A':
                regs.append(primitive(op, a, vals[1]))
            elif action == 'S':
                stores.append((a, vals[1]))
            elif action == 'B':
                pred = np.broadcast_to(primitive(op, a, vals[1]), self.sat.shape)
                agree &= pred == pred[base]
            elif action == 'L':
                val = np.int32(0)
                for j, column in enumerate(self.original):
                    val = np.where(a == j, column, val)
                for written, value in stores:
                    val = np.where(a == written, value, val)
                regs.append(val)
            else:
                raise ValueError(action)
        return np.flatnonzero(agree)
