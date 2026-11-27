"""One interpreter for the journal's native machine (standing-opponent suite).

Machine, as fixed in notes/native-unary-clock-band.md ("For definiteness ..."):
word width w (the suite uses w = 12*ceil(log2(T+2)) for clock T), a fixed
register file (16 registers r0..r15, all starting at 0), a read-only input of
words, zero-initialised addressable work words, unit cost per instruction.

Instruction records (tuples):
  ('li', d, imm)            d := imm mod 2^w
  ('mov', d, a)  ('not', d, a)
  (op, d, a, b)             op in ALU3 below, d := a op b
  (op+'i', d, a, imm)       same with an immediate second operand
  ('inlen', d)              d := number of input words (public: the length)
  ('ldin', d, a)            d := input[a]  (0 beyond the end)      [input read]
  ('ld', d, a)              d := mem[a]                            [work load]
  ('st', a, b)              mem[a] := b                            [work store]
  ('lic', d, a, name)       d := CONST[name][a mod len]  (fixed constant table of
                            the program text; charged ceil(log2 len)+1 steps, the
                            cost of a fixed public binary-search selection)
  ('jmp', L) ('bz', a, L) ('bnz', a, L) ('bltu', a, b, L)
  ('halt', a)               output := a
ALU3: add sub mul divu modu and or xor shl shr rol ror eq ltu.
divu by 0 gives 0 and modu by 0 gives a (fixed zero-divisor semantics);
shl/shr by >= w give 0; rol/ror rotate by b mod w; eq/ltu give 0/1.

Taint, for the nonlinear depth of the path-parity games.  Every register and
cell carries (kind, depth): kind 'P' public (computed from constants and the
input length only), 'F' fresh variable (input word, or result of a nonlinear
event), 'X' GF(2)-affine in fresh variables, 'A' Z/2^w-affine in fresh
variables.  Nonlinear events (depth := max operand depth + 1, kind := 'F'):
AND/OR/MUL/DIV/MOD/compare of two data words, shift or rotate by a data
amount, an X-value entering + or * (or an A-value entering XOR/AND/OR/shr/rot):
"+ meets XOR", a load/store/input read at a data-dependent address.
A branch on data is an event of depth (cond depth + 1); it is recorded but NOT
propagated into later values (no implicit-flow tracking), so the reported depth
is a lower estimate of that depth when control flow diverges on data.
"""

ALU3 = ('add', 'sub', 'mul', 'divu', 'modu', 'and', 'or', 'xor',
        'shl', 'shr', 'rol', 'ror', 'eq', 'ltu')
PUB = ('P', 0)


class Program:
    def __init__(self, lines, consts=None):
        self.code, self.labels = [], {}
        for ln in lines:
            if isinstance(ln, str):
                assert ln.endswith(':'), ln
                self.labels[ln[:-1]] = len(self.code)
            else:
                self.code.append(ln)
        self.consts = consts or {}
        for ins in self.code:   # resolve jump targets now
            if ins[0] in ('jmp', 'bz', 'bnz', 'bltu'):
                assert ins[-1] in self.labels, ins


def alu(op, a, b, w, mask):
    if op == 'add':
        return (a + b) & mask
    if op == 'sub':
        return (a - b) & mask
    if op == 'mul':
        return (a * b) & mask
    if op == 'divu':
        return a // b if b else 0
    if op == 'modu':
        return a % b if b else a
    if op == 'and':
        return a & b
    if op == 'or':
        return a | b
    if op == 'xor':
        return a ^ b
    if op == 'shl':
        return (a << b) & mask if b < w else 0
    if op == 'shr':
        return a >> b if b < w else 0
    if op == 'rol':
        s = b % w
        return ((a << s) | (a >> (w - s))) & mask if s else a
    if op == 'ror':
        s = b % w
        return ((a >> s) | (a << (w - s))) & mask if s else a
    if op == 'eq':
        return 1 if a == b else 0
    if op == 'ltu':
        return 1 if a < b else 0
    raise ValueError(op)


def combine(op, ta, tb, vb):
    """Taint of (a op b).  Returns (taint, is_event)."""
    ka, da = ta
    kb, db = tb
    if ka == 'P' and kb == 'P':
        return PUB, False
    d = max(da, db)
    one_pub = (ka == 'P') or (kb == 'P')
    k = kb if ka == 'P' else ka            # the data operand's kind when one_pub
    if op in ('and', 'or', 'xor'):
        if one_pub:
            return (('X', d), False) if k in ('F', 'X') else (('F', d + 1), True)
        if op == 'xor' and ka in ('F', 'X') and kb in ('F', 'X'):
            return ('X', d), False
        return ('F', d + 1), True
    if op in ('add', 'sub'):
        if one_pub:
            return (('A', d), False) if k in ('F', 'A') else (('F', d + 1), True)
        if ka in ('F', 'A') and kb in ('F', 'A'):
            return ('A', d), False
        return ('F', d + 1), True
    if op == 'mul':
        if one_pub:
            return (('A', d), False) if k in ('F', 'A') else (('F', d + 1), True)
        return ('F', d + 1), True
    if op in ('shl', 'shr', 'rol', 'ror'):
        if kb != 'P':
            return ('F', d + 1), True        # data-dependent amount
        if op == 'shl':
            return (ka, d), False            # times 2^k: linear in both structures
        return (('X', d), False) if ka in ('F', 'X') else (('F', d + 1), True)
    if op in ('divu', 'modu'):
        if kb == 'P' and vb > 0 and (vb & (vb - 1)) == 0:
            return (('X', d), False) if ka in ('F', 'X') else (('F', d + 1), True)
        return ('F', d + 1), True
    if op in ('eq', 'ltu'):
        return ('F', d + 1), True
    raise ValueError(op)


class Machine:
    def __init__(self, prog, inp, w, nregs=16, pc=0, regs=None):
        self.p, self.code, self.lab = prog, prog.code, prog.labels
        self.w, self.mask = w, (1 << w) - 1
        self.inp = [v & self.mask for v in inp]
        self.reg = list(regs) if regs else [0] * nregs
        self.rt = [PUB] * nregs
        self.mem, self.mt = {}, {}
        self.pc, self.halted, self.output = pc, False, None
        self.steps = 0            # instruction count (lic charged as a selection)
        self.acc = []             # work-memory accesses: (kind, addr, value, step)
        self.inreads = 0
        self.nonzero = 0
        self.space_max = 0
        self.maxdepth = 0
        self.events = 0
        self.branch_depth = 0
        self.load_override = None  # used by an extraction harness only (not part of the suite)

    def _note(self, t):
        if t[1] > self.maxdepth:
            self.maxdepth = t[1]

    def peek(self):
        return self.code[self.pc]

    def step(self):
        ins = self.code[self.pc]
        op = ins[0]
        R, RT, m = self.reg, self.rt, self.mask
        self.pc += 1
        self.steps += 1
        if op == 'li':
            R[ins[1]], RT[ins[1]] = ins[2] & m, PUB
        elif op == 'mov':
            R[ins[1]], RT[ins[1]] = R[ins[2]], RT[ins[2]]
        elif op == 'not':
            R[ins[1]], RT[ins[1]] = (~R[ins[2]]) & m, RT[ins[2]]
        elif op in ALU3 or (op.endswith('i') and op[:-1] in ALU3):
            base = op if op in ALU3 else op[:-1]
            a, ta = R[ins[2]], RT[ins[2]]
            if op in ALU3:
                b, tb = R[ins[3]], RT[ins[3]]
            else:
                b, tb = ins[3] & m, PUB
            R[ins[1]] = alu(base, a, b, self.w, m)
            t, ev = combine(base, ta, tb, b)
            RT[ins[1]] = t
            self.events += ev
            self._note(t)
        elif op == 'inlen':
            R[ins[1]], RT[ins[1]] = len(self.inp) & m, PUB
        elif op == 'ldin':
            a, ta = R[ins[2]], RT[ins[2]]
            R[ins[1]] = self.inp[a] if a < len(self.inp) else 0
            if ta[0] == 'P':
                RT[ins[1]] = ('F', 0)
            else:
                RT[ins[1]] = ('F', ta[1] + 1)
                self.events += 1
            self._note(RT[ins[1]])
            self.inreads += 1
        elif op == 'ld':
            a, ta = R[ins[2]], RT[ins[2]]
            v = self.mem.get(a, 0)
            if self.load_override is not None:
                v, self.load_override = self.load_override & m, None
            tc = self.mt.get(a, PUB)
            if ta[0] == 'P':
                t = tc
            else:
                t = ('F', max(ta[1], tc[1]) + 1)
                self.events += 1
            R[ins[1]], RT[ins[1]] = v, t
            self._note(t)
            self.acc.append(('ld', a, v, self.steps))
        elif op == 'st':
            a, ta = R[ins[1]], RT[ins[1]]
            v, tv = R[ins[2]], RT[ins[2]]
            old = self.mem.get(a, 0)
            self.nonzero += (v != 0) - (old != 0)
            if self.nonzero > self.space_max:
                self.space_max = self.nonzero
            self.mem[a] = v
            if ta[0] == 'P':
                self.mt[a] = tv
            else:
                self.mt[a] = ('F', max(ta[1], tv[1]) + 1)
                self.events += 1
                self._note(self.mt[a])
            self.acc.append(('st', a, v, self.steps))
        elif op == 'lic':
            tab = self.p.consts[ins[3]]
            a, ta = R[ins[2]], RT[ins[2]]
            R[ins[1]] = tab[a % len(tab)] & m
            RT[ins[1]] = PUB if ta[0] == 'P' else ('F', ta[1] + 1)
            self.steps += max(1, (len(tab) - 1).bit_length())  # selection cost
        elif op == 'jmp':
            self.pc = self.lab[ins[1]]
        elif op in ('bz', 'bnz'):
            a, ta = R[ins[1]], RT[ins[1]]
            if ta[0] != 'P':
                self.events += 1
                self.branch_depth = max(self.branch_depth, ta[1] + 1)
            if (a == 0) == (op == 'bz'):
                self.pc = self.lab[ins[2]]
        elif op == 'bltu':
            ta, tb = RT[ins[1]], RT[ins[2]]
            if ta[0] != 'P' or tb[0] != 'P':
                self.events += 1
                self.branch_depth = max(self.branch_depth, max(ta[1], tb[1]) + 1)
            if R[ins[1]] < R[ins[2]]:
                self.pc = self.lab[ins[3]]
        elif op == 'halt':
            self.halted, self.output = True, R[ins[1]]
            self.pc -= 1
        else:
            raise ValueError(ins)

    def run(self, max_acc=None, max_steps=10 ** 8):
        """Run until halt, or until the work-access count reaches max_acc
        (the clock of the truncated opponent prefix)."""
        while not self.halted and self.steps < max_steps:
            if max_acc is not None and len(self.acc) >= max_acc:
                break
            self.step()
        return self


def width_for_clock(T):
    return 12 * (T + 2 - 1).bit_length()   # 12*ceil(log2(T+2))
