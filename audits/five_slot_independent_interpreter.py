#!/usr/bin/env python3
"""Independent interpreter for the five-slot separate-operation RAM, written during review from the
definition quoted in notes/five-instructions-cannot-decide-dimacs-sat.md and the conventions of
the 43-instruction note (registers zero, no public n/w, register STORE payloads, free fixed
successors, YES/NO uncounted terminals, literals mod 2^w).  Memory: a base function (input
words, zero elsewhere) plus a dict of writes.  Shifts: both catalog conventions are computed
and the run aborts if they disagree (count >= w)."""
import re

DATA_OPS = {'add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr', 'eq', 'ne', 'ltu', 'mov'}
BR = {'eq', 'ne', 'ltu', 'geu'}


def assemble(text):
    rows = []
    for line in text.split('\n'):
        line = line.split('#')[0].strip()
        if not line:
            continue
        lab = None
        if re.match(r'^\w+:', line):
            lab, line = line.split(':', 1)
            line = line.strip()
        succ = None
        if '->' in line:
            line, succ = [s.strip() for s in line.split('->')]
        rows.append((lab, line.split(), succ))
    where = {lab: i for i, (lab, _, _) in enumerate(rows) if lab}
    assert len(where) == sum(1 for r in rows if r[0])

    def T(s):
        return s if s in ('YES', 'NO') else where[s]

    def O(s):
        if re.fullmatch(r'-?\d+', s):
            return ('lit', int(s))
        assert re.fullmatch(r'[a-z]\w*', s)
        return ('reg', s)

    code = []
    for i, (lab, tok, succ) in enumerate(rows):
        nxt = T(succ) if succ else i + 1
        if tok[0] == 'br':
            assert len(tok) == 6 and tok[1] in BR and succ is None
            code.append(('B', tok[1], O(tok[2]), O(tok[3]), T(tok[4]), T(tok[5])))
        elif tok[0] == 'store':
            assert len(tok) == 3 and O(tok[2])[0] == 'reg'      # payload is a register
            code.append(('S', O(tok[1]), O(tok[2]), nxt))
        else:
            assert tok[1] == '=' and O(tok[0])[0] == 'reg'
            if tok[2] == 'load':
                assert len(tok) == 4
                code.append(('L', tok[0], O(tok[3]), nxt))
            else:
                assert tok[2] in DATA_OPS and 4 <= len(tok) <= 5   # at most two operands
                code.append(('N', tok[0], tok[2], [O(t) for t in tok[3:]], nxt))
    for c in code:
        for t in (c[4:6] if c[0] == 'B' else c[-1:]):
            assert t in ('YES', 'NO') or 0 <= t < len(code)
    return code


def execute(code, w, base, cap):
    """base(a) -> original word at address a (0 outside the file). Returns (verdict, steps, regs)."""
    Q = 1 << w
    M = Q - 1
    regs, writes = {}, {}
    pc, steps = 0, 0

    def val(o):
        return (o[1] % Q) if o[0] == 'lit' else regs.get(o[1], 0)

    def mem(a):
        return writes[a] if a in writes else base(a)

    while pc not in ('YES', 'NO'):
        if steps >= cap:
            return 'CAP', steps, regs
        steps += 1
        c = code[pc]
        if c[0] == 'L':
            regs[c[1]] = mem(val(c[2])); pc = c[3]
        elif c[0] == 'S':
            writes[val(c[1])] = val(c[2]); pc = c[3]
        elif c[0] == 'N':
            ops = [val(o) for o in c[3]]
            a = ops[0]; b = ops[1] if len(ops) > 1 else 0
            op = c[2]
            if op in ('shl', 'shr'):
                sat = ((a << b) & M if b < w else 0) if op == 'shl' else (a >> b if b < w else 0)
                k = b % w
                modw = (a << k) & M if op == 'shl' else a >> k
                assert sat == modw, 'shift conventions disagree'
                r = sat
            else:
                r = {'add': (a + b) & M, 'sub': (a - b) & M, 'mul': (a * b) & M, 'and': a & b,
                     'or': a | b, 'xor': a ^ b, 'eq': int(a == b), 'ne': int(a != b),
                     'ltu': int(a < b), 'mov': a}[op]
            regs[c[1]] = r; pc = c[4]
        else:
            a, b = val(c[2]), val(c[3])
            t = {'eq': a == b, 'ne': a != b, 'ltu': a < b, 'geu': a >= b}[c[1]]
            pc = c[4] if t else c[5]
    return pc, steps, regs


def file_base(data, w):
    W = w // 8
    words = {}
    for k in range(0, len(data), W):
        v = int.from_bytes(data[k:k + W], 'little')
        if v:
            words[k // W] = v
    return lambda a: words.get(a, 0)


def count(code):
    return len(code)
