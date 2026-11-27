#!/usr/bin/env python3
"""Per-path affine-flat bound for a toy word RAM with branches and indirect addressing.

Values are words of w affine forms over F_2 in the input bits (int bitmask: bits 0..n-1 =
coefficients, bit n = constant). A flat is a reduced system of affine equations.
Free: XOR/XORI/ANDI(const mask)/SHL/SHR by constants/MOVI, loads/stores at constant addresses.
Charged (cost = equations added to keep everything affine and control constant):
  AND (<= w), ADD (<= w-1), BRZ with nonconstant control (existential: 1; through-x: <= w),
  LD/ST with nonconstant address (<= w).
Two procedures:
  existential: choose values freely -> a flat F on which f is affine; lambda(f) <= codim F.
  through-x  : fix values to those of a given input x -> a flat through x.
Verification by brute force over all 2^n inputs: every input of F follows the same PC trace,
the program output equals the symbolic affine output on F, codim F <= sum of costs <= w * charged.
Also runs the two MUX_k programs (one indirect load; k one-bit branches + known-address load).
Written for the-instruction-capacity-line-is-capped-at-a-packed-scan.md.
"""
import random, sys

class Flat:
    def __init__(self, n):
        self.n = n
        self.eqs = {}  # pivot -> form (form(x) = 0 on the flat)
    def reduce(self, f):
        for p, e in self.eqs.items():
            if (f >> p) & 1:
                f ^= e
        return f
    def varpart(self, f):
        return f & ((1 << self.n) - 1)
    def is_const(self, f):
        return self.varpart(self.reduce(f)) == 0
    def const_val(self, f):
        return (self.reduce(f) >> self.n) & 1
    def add(self, f):
        """impose f(x) = 0; returns 1 if a new independent equation was added, 0 if redundant."""
        f = self.reduce(f)
        if self.varpart(f) == 0:
            assert (f >> self.n) & 1 == 0, "inconsistent equation"
            return 0
        p = self.varpart(f).bit_length() - 1
        for q in list(self.eqs):
            if (self.eqs[q] >> p) & 1:
                self.eqs[q] ^= f
        self.eqs[p] = f
        return 1
    def contains(self, x):
        for e in self.eqs.values():
            if evalf(e, x, self.n):
                return False
        return True

def evalf(f, x, n):
    return (bin(f & x).count("1") + ((f >> n) & 1)) & 1

def const_form(b, n):
    return (b & 1) << n

# ---------------- concrete interpreter ----------------
def run_concrete(prog, x, n, w, nin):
    mask = (1 << w) - 1
    M = {j: (x >> (j * w)) & mask for j in range(nin)}
    R = [0, 0, 0, 0]
    pc, trace = 0, []
    while True:
        trace.append(pc)
        ins = prog[pc]
        op = ins[0]
        if op == 'LDI': R[ins[1]] = M.get(ins[2], 0)
        elif op == 'LD': R[ins[1]] = M.get(R[ins[2]], 0)
        elif op == 'STI': M[ins[1]] = R[ins[2]]
        elif op == 'ST': M[R[ins[1]]] = R[ins[2]]
        elif op == 'XOR': R[ins[1]] = R[ins[2]] ^ R[ins[3]]
        elif op == 'XORI': R[ins[1]] = (R[ins[2]] ^ ins[3]) & mask
        elif op == 'ANDI': R[ins[1]] = R[ins[2]] & ins[3]
        elif op == 'SHL': R[ins[1]] = (R[ins[2]] << ins[3]) & mask
        elif op == 'SHR': R[ins[1]] = R[ins[2]] >> ins[3]
        elif op == 'MOVI': R[ins[1]] = ins[2] & mask
        elif op == 'AND': R[ins[1]] = R[ins[2]] & R[ins[3]]
        elif op == 'ADD': R[ins[1]] = (R[ins[2]] + R[ins[3]]) & mask
        elif op == 'BRZ':
            if R[ins[1]] == 0:
                pc = ins[2]; continue
        elif op == 'HALT':
            return R[ins[1]] & 1, trace
        pc += 1

# ---------------- symbolic per-path procedure ----------------
def run_symbolic(prog, n, w, nin, x0=None):
    """x0 None: existential choices; else through-x0. Returns (flat, out_form, trace, cost, charged)."""
    F = Flat(n)
    def inword(j):
        return [(1 << (j * w + i)) if j * w + i < n else 0 for i in range(w)]
    zero = [0] * w
    M = {j: inword(j) for j in range(nin)}
    R = [list(zero) for _ in range(4)]
    pc, trace, cost, charged = 0, [], 0, 0
    def xval(f):
        return evalf(f, x0, n)
    def fix_nonconst(word, values=None):
        c = 0
        for i, f in enumerate(word):
            if not F.is_const(f):
                v = values[i] if values is not None else 0
                c += F.add(f ^ const_form(v, n))
        return c
    def word_int(word):
        return sum(F.const_val(f) << i for i, f in enumerate(word))
    def mul_affine(u, v):
        """returns (form for u*v, cost) keeping flat nonempty and product affine on it."""
        if F.is_const(u):
            return (v if F.const_val(u) else 0), 0
        if F.is_const(v):
            return (u if F.const_val(v) else 0), 0
        d = u ^ v
        if F.is_const(d):  # v = u + c
            return (u if F.const_val(d) == 0 else 0), 0
        val = xval(u) if x0 is not None else 0
        c = F.add(u ^ const_form(val, n))
        return (v if val else 0), c
    while True:
        trace.append(pc)
        ins = prog[pc]
        op = ins[0]
        if op == 'LDI': R[ins[1]] = list(M.get(ins[2], zero))
        elif op in ('LD', 'ST'):
            aw = R[ins[2]] if op == 'LD' else R[ins[1]]
            if any(not F.is_const(f) for f in aw):
                charged += 1
                vals = [xval(f) for f in aw] if x0 is not None else None
                cost += fix_nonconst(aw, vals)
            a = word_int(aw)
            if op == 'LD': R[ins[1]] = list(M.get(a, zero))
            else: M[a] = list(R[ins[2]])
        elif op == 'STI': M[ins[1]] = list(R[ins[2]])
        elif op == 'XOR': R[ins[1]] = [p ^ q for p, q in zip(R[ins[2]], R[ins[3]])]
        elif op == 'XORI': R[ins[1]] = [p ^ const_form((ins[3] >> i) & 1, n) for i, p in enumerate(R[ins[2]])]
        elif op == 'ANDI': R[ins[1]] = [p if (ins[3] >> i) & 1 else 0 for i, p in enumerate(R[ins[2]])]
        elif op == 'SHL': R[ins[1]] = [0] * ins[3] + R[ins[2]][:w - ins[3]]
        elif op == 'SHR': R[ins[1]] = R[ins[2]][ins[3]:] + [0] * ins[3]
        elif op == 'MOVI': R[ins[1]] = [const_form((ins[2] >> i) & 1, n) for i in range(w)]
        elif op == 'AND':
            charged += 1
            out = []
            for i in range(w):
                p, c = mul_affine(R[ins[2]][i], R[ins[3]][i]); cost += c; out.append(p)
            R[ins[1]] = out
        elif op == 'ADD':
            charged += 1
            a, b = R[ins[2]], R[ins[3]]
            car, out = 0, []
            for i in range(w):
                out.append(a[i] ^ b[i] ^ car)
                if i < w - 1:
                    p, c = mul_affine(a[i] ^ car, b[i] ^ car); cost += c
                    car = p ^ car
            R[ins[1]] = out
        elif op == 'BRZ':
            word = R[ins[1]]
            if all(F.is_const(f) for f in word):
                if word_int(word) == 0:
                    pc = ins[2]; continue
            else:
                charged += 1
                if x0 is None:
                    i = next(i for i, f in enumerate(word) if not F.is_const(f))
                    cost += F.add(word[i] ^ const_form(1, n))   # force nonzero: branch not taken
                else:
                    xv = [xval(f) for f in word]
                    if any(xv):
                        if not any(F.is_const(f) and F.const_val(f) == 1 for f in word):
                            i = next(i for i, f in enumerate(word) if xv[i] == 1)
                            cost += F.add(word[i] ^ const_form(1, n))
                    else:
                        cost += fix_nonconst(word, xv)
                        pc = ins[2]; continue
        elif op == 'HALT':
            return F, F.reduce(R[ins[1]][0]), trace, cost, charged
        pc += 1

def verify(prog, n, w, nin, F, out, trace, x0=None):
    members = 0
    for x in range(1 << n):
        if not F.contains(x):
            continue
        members += 1
        o, t = run_concrete(prog, x, n, w, nin)
        if t != trace or o != evalf(out, x, n):
            return False, members
    if x0 is not None and not F.contains(x0):
        return False, members
    return members == (1 << (n - len(F.eqs))), members

# ---------------- random programs ----------------
def random_program(rng, n, w, nin, length):
    mask = (1 << w) - 1
    prog = [('LDI', r % 4, r % nin) for r in range(min(4, nin + 2))]
    body = []
    for _ in range(length):
        op = rng.choice(['XOR', 'XORI', 'ANDI', 'SHL', 'SHR', 'AND', 'AND', 'ADD', 'ADD',
                         'BRZ', 'LD', 'ST', 'STI', 'LDI'])
        r, s, t = rng.randrange(4), rng.randrange(4), rng.randrange(4)
        if op == 'XOR': body.append(('XOR', r, s, t))
        elif op == 'XORI': body.append(('XORI', r, s, rng.randrange(1 << w)))
        elif op == 'ANDI': body.append(('ANDI', r, s, rng.randrange(1 << w)))
        elif op in ('SHL', 'SHR'): body.append((op, r, s, rng.randrange(1, w)))
        elif op in ('AND', 'ADD'): body.append((op, r, s, t))
        elif op == 'BRZ': body.append(('BRZ', r, None))
        elif op == 'LD': body.append(('LD', r, s))
        elif op == 'ST': body.append(('ST', r, s))
        elif op == 'STI': body.append(('STI', rng.randrange(nin + 3), r))
        elif op == 'LDI': body.append(('LDI', r, rng.randrange(nin + 3)))
    prog += body
    prog.append(('HALT', rng.randrange(4)))
    L = len(prog)
    prog = [(ins[0], ins[1], rng.randrange(i + 1, L)) if ins[0] == 'BRZ' else ins for i, ins in enumerate(prog)]
    return prog

def mux_indirect(k, w):
    # input: T (2^k bits) then index i (k bits); unpack T one bit per word at base 32 (free), then one LD
    K = 1 << k
    n = K + k
    nin = (n + w - 1) // w
    base = 64
    prog = []
    for t in range(K):
        prog += [('LDI', 0, t // w), ('SHR', 0, 0, t % w), ('ANDI', 0, 0, 1), ('STI', base + t, 0)]
    # gather index bits into register 1 (free: shifts, masks, xor by constants)
    prog += [('MOVI', 1, 0)]
    for j in range(k):
        pos = K + j
        prog += [('LDI', 2, pos // w), ('SHR', 2, 2, pos % w), ('ANDI', 2, 2, 1), ('SHL', 2, 2, j), ('XOR', 1, 1, 2)]
    prog += [('XORI', 1, 1, base), ('LD', 3, 1), ('HALT', 3)]
    return prog, n, nin

def mux_branches(k, w):
    K = 1 << k
    n = K + k
    nin = (n + w - 1) // w
    base = 64
    prog = []
    for t in range(K):
        prog += [('LDI', 0, t // w), ('SHR', 0, 0, t % w), ('ANDI', 0, 0, 1), ('STI', base + t, 0)]
    prog += [('MOVI', 1, base)]
    for j in range(k):
        pos = K + j
        prog += [('LDI', 2, pos // w), ('SHR', 2, 2, pos % w), ('ANDI', 2, 2, 1)]
        here = len(prog)
        prog += [('BRZ', 2, here + 2), ('XORI', 1, 1, 1 << j)]
    prog += [('LD', 3, 1), ('HALT', 3)]
    return prog, n, nin

if __name__ == "__main__":
    rng = random.Random(20261127)
    hist = {}
    stats = {'programs': 0, 'exist_ok': 0, 'thru_checks': 0, 'thru_ok': 0, 'max_ratio': 0.0,
             'max_codim': 0, 'bound_ok': True}
    for trial in range(400):
        n, w = rng.choice([(6, 3), (8, 4), (6, 2)])
        nin = (n + w - 1) // w
        prog = random_program(rng, n, w, nin, rng.randrange(8, 20))
        # ensure addresses stay small: (LD/ST use raw register values; memory is a dict, fine)
        F, out, tr, cost, ch = run_symbolic(prog, n, w, nin, None)
        ok, mem = verify(prog, n, w, nin, F, out, tr)
        stats['programs'] += 1
        codim = len(F.eqs)
        if ok and codim <= cost <= w * ch:
            stats['exist_ok'] += 1
        else:
            stats['bound_ok'] = False
            print("EXISTENTIAL FAILURE", prog, codim, cost, ch); break
        stats['max_codim'] = max(stats['max_codim'], codim)
        hist[ch] = hist.get(ch, 0) + 1
        for x0 in rng.sample(range(1 << n), 6):
            F2, out2, tr2, cost2, ch2 = run_symbolic(prog, n, w, nin, x0)
            ok2, _ = verify(prog, n, w, nin, F2, out2, tr2, x0)
            stats['thru_checks'] += 1
            if ok2 and len(F2.eqs) <= cost2 <= w * ch2:
                stats['thru_ok'] += 1
                if ch2:
                    stats['max_ratio'] = max(stats['max_ratio'], len(F2.eqs) / (w * ch2))
            else:
                stats['bound_ok'] = False
                print("THROUGH-X FAILURE", prog, x0); break
    print("random programs:", stats)
    print("existential charged-count histogram:", dict(sorted(hist.items())))
    for k, w in [(2, 8), (3, 8)]:
        for name, builder in [('one indirect load', mux_indirect), ('k one-bit branches', mux_branches)]:
            prog, n, nin = builder(k, w)
            correct = all(run_concrete(prog, x, n, w, nin)[0] == (x >> ((x >> (1 << k)) & ((1 << k) - 1))) & 1
                          for x in range(1 << n))
            F, out, tr, cost, ch = run_symbolic(prog, n, w, nin, None)
            ok, mem = verify(prog, n, w, nin, F, out, tr)
            worst_thru = 0
            for x0 in range(1 << n):
                F2, o2, t2, c2, ch2 = run_symbolic(prog, n, w, nin, x0)
                worst_thru = max(worst_thru, ch2)
            print(f"MUX_{k} via {name} (w={w}, n={n}): computes MUX: {correct}; existential path: charged={ch}, "
                  f"codim={len(F.eqs)}, verified={ok}; max charged over all inputs={worst_thru}; MC(MUX_{k})=2^k-1={2**k-1}")
