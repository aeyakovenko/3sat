"""Interpreter for the journal's separate-operation word RAM (five-slot notes), written for
a-43-instruction-sat-program-in-the-five-slot-machine.md.

Machine, as implemented (hardest reading where the notes leave a choice):
  * width w = 16*ceil(log2(n+2)/16), n = 8 * (bytes of the file); memory 2^w words,
    input packed little-endian, W = w/8 bytes per word, from address 0; zero elsewhere.
  * registers: unboundedly many, all zero initially; NO public n or w is supplied.
  * LOAD  r <- M[A]       A = register or literal
  * STORE M[A] <- r       A = register or literal; payload a REGISTER (no literal payload)
  * numerical site r <- op(X, Y), X,Y registers or literals (literals reduced mod 2^w)
        ops: add sub mul and or xor shl shr eq ne ltu mov
        shl/shr: count taken as a full word; counts >= w give 0 (saturating). The
        programs here only use the literal count 8 < 16 <= w, so both shift
        conventions of the native catalog agree.
        eq/ne/ltu write 1 or 0.
  * branch: compare X, Y (eq ne ltu geu), two fixed successors.
  * every non-branch instruction has one fixed successor; YES/NO are free terminals.
Assembly format (one stored instruction per non-empty line):
  [LABEL:] r = op X Y [-> L]      r = load A [-> L]      store A r [-> L]
  [LABEL:] br cmp X Y LT LF      (LT/LF are labels, YES or NO)
"""
import re

OPS = {'add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr', 'eq', 'ne', 'ltu', 'mov'}
CMPS = {'eq', 'ne', 'ltu', 'geu'}


def parse(text):
    lines = []
    for raw in text.splitlines():
        s = raw.split('#', 1)[0].strip()
        if not s:
            continue
        lab = None
        m = re.match(r'^([A-Za-z_][A-Za-z0-9_]*):\s*(.*)$', s)
        if m:
            lab, s = m.group(1), m.group(2)
        lines.append((lab, s))
    labels = {}
    for k, (lab, _) in enumerate(lines):
        if lab:
            assert lab not in labels, lab
            labels[lab] = k

    def tgt(t):
        if t in ('YES', 'NO'):
            return t
        return labels[t]

    def opd(t):
        if re.match(r'^-?\d+$', t):
            return ('i', int(t))
        assert re.match(r'^[a-z][a-z0-9]*$', t), t
        return ('r', t)

    prog = []
    for k, (lab, s) in enumerate(lines):
        nxt = k + 1
        if '->' in s:
            s, t = s.split('->')
            s = s.strip()
            nxt = tgt(t.strip())
        tok = s.split()
        if tok[0] == 'br':
            _, c, x, y, lt, lf = tok
            assert c in CMPS
            prog.append(('br', c, opd(x), opd(y), tgt(lt), tgt(lf)))
        elif tok[0] == 'store':
            _, a, v = tok
            assert opd(v)[0] == 'r', 'store payload must be a register'
            prog.append(('store', opd(a), opd(v), nxt))
        else:
            assert tok[1] == '='
            dst = tok[0]
            assert re.match(r'^[a-z][a-z0-9]*$', dst)
            if tok[2] == 'load':
                prog.append(('load', dst, opd(tok[3]), nxt))
            else:
                op = tok[2]
                assert op in OPS, op
                x = opd(tok[3])
                y = opd(tok[4]) if len(tok) > 4 else ('i', 0)
                assert len(tok) <= 5
                prog.append(('op', dst, op, x, y, nxt))
    for ins in prog:  # every successor must exist
        for t in ins[-2:] if ins[0] == 'br' else ins[-1:]:
            assert t in ('YES', 'NO') or 0 <= t < len(prog), (ins, t)
    return prog


def width_for(nbytes):
    n = 8 * nbytes
    L = (n + 2 - 1).bit_length()  # ceil(log2(n+2))
    return 16 * ((L + 15) // 16)


def run(prog, data, w=None, max_steps=10**9):
    """Run on file bytes `data`. Returns (verdict, steps)."""
    if w is None:
        w = width_for(len(data))
    assert w % 8 == 0
    W = w // 8
    Q = 1 << w
    mask = Q - 1
    mem = {}
    for k in range(0, len(data), W):
        chunk = data[k:k + W]
        v = int.from_bytes(chunk, 'little')
        if v:
            mem[k // W] = v
    reg = {}
    pc = 0
    steps = 0

    def val(o):
        return o[1] & mask if o[0] == 'i' else reg.get(o[1], 0)

    while True:
        if pc == 'YES' or pc == 'NO':
            return pc, steps
        if steps >= max_steps:
            return 'TIMEOUT', steps
        steps += 1
        ins = prog[pc]
        k = ins[0]
        if k == 'op':
            _, d, op, x, y, nxt = ins
            a, b = val(x), val(y)
            if op == 'add':
                r = (a + b) & mask
            elif op == 'sub':
                r = (a - b) & mask
            elif op == 'mul':
                r = (a * b) & mask
            elif op == 'and':
                r = a & b
            elif op == 'or':
                r = a | b
            elif op == 'xor':
                r = a ^ b
            elif op == 'shl':
                r = (a << b) & mask if b < w else 0
            elif op == 'shr':
                r = a >> b if b < w else 0
            elif op == 'eq':
                r = int(a == b)
            elif op == 'ne':
                r = int(a != b)
            elif op == 'ltu':
                r = int(a < b)
            elif op == 'mov':
                r = a
            reg[d] = r
            pc = nxt
        elif k == 'load':
            _, d, A, nxt = ins
            reg[d] = mem.get(val(A), 0)
            pc = nxt
        elif k == 'store':
            _, A, V, nxt = ins
            v = val(V)
            a = val(A)
            if v:
                mem[a] = v
            else:
                mem.pop(a, None)
            pc = nxt
        else:
            _, c, x, y, lt, lf = ins
            a, b = val(x), val(y)
            if c == 'eq':
                t = a == b
            elif c == 'ne':
                t = a != b
            elif c == 'ltu':
                t = a < b
            else:
                t = a >= b
            pc = lt if t else lf
