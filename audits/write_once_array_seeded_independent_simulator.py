"""Independent multi-level simulator of the seeded packed-presence-table array (Z1+) of
notes/ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md, written during review from the note's
description of the scheme (after reading the one-level simulator write_once_array_seeded_level_costs.cpp).

Run from audits/:
  python3 write_once_array_seeded_independent_simulator.py
      the default suite, about 10 s: mode cost at w = 32, B = 4, n = 2048 (2 seeds, six families), mode bad at
      w = 32, B = 4, n = 1024 (six bad seeds, six families) and mode neg; exits 1 if a good seed errs, a bad
      seed breaks legality or correctness, or a negative control does not abort.
  python3 write_once_array_seeded_independent_simulator.py cost W BETA N SEEDS FAMILIES   (FAMILIES comma-separated)
  python3 write_once_array_seeded_independent_simulator.py bad W BETA N
  python3 write_once_array_seeded_independent_simulator.py neg W BETA N
Families: uni, rep, ap, cons, hot, absent. Nothing is written.
"""
# Every structure lives in one write-once integer memory with the note's layout:
#   region (kind, level) at (3*level + kind) * 2^RS, RS = w - ceil(log2(3(w/beta+1))) - 1, bit-scan table at 2^(w-1).
# Memory aborts on a second write or on a load of an unwritten cell. Probes are counted as Section 3 of the note does:
# 2 loads per scanned entry (h', x), 2 directory cells, 1 table load per bit scan, 1 presence word per level, ...
# Hash: Barrett reduction of a*x^2 + b*x + c modulo p, exactly the note's formulas, with wrap-around for bad seeds.
import sys, math, random
from sympy import nextprime, isprime

class Violation(Exception):
    pass

class Mem:
    def __init__(self, w):
        self.w = w; self.cells = {}; self.loads = 0; self.writes = 0
    def load(self, a):
        if a not in self.cells:
            raise Violation("load of unwritten cell %d" % a)
        self.loads += 1
        return self.cells[a]
    def write(self, a, v):
        if a in self.cells:
            raise Violation("second write of cell %d" % a)
        if not (0 <= a < (1 << self.w)):
            raise Violation("address out of range %d" % a)
        self.writes += 1
        self.cells[a] = v

class Z1plus:
    def __init__(self, w, beta, seed, check_layout=True):
        self.w = w; self.beta = beta; self.B = 1 << beta
        assert self.B * self.B <= w
        p, rho, a, b, c = seed
        self.p, self.rho, self.a, self.b, self.c = p, rho, a, b, c
        self.k = w + 1
        self.mask3 = (1 << (3 * w)) - 1
        self.m = Mem(w)
        L = w // beta + 1
        self.RS = w - math.ceil(math.log2(3 * L)) - 1
        self.U = 0
        self.check_layout = check_layout
        self.tab = 1 << (w - 1)
        B = self.B
        # bit-scan table TAB[v] = index of lowest set bit, v in [1, 2^B), written once, each loads an earlier cell
        for v in range(1, 1 << B):
            if v & 1:
                self.m.write(self.tab + v, 0)
            else:
                self.m.write(self.tab + v, self.m.load(self.tab + (v >> 1)) + 1)
        self.init_probes = self.m.loads + self.m.writes
        self.m.loads = 0; self.m.writes = 0
        self.good_reductions = True

    # ---------------- hash ----------------
    def red(self, z):
        k = self.k
        z1 = z >> (k - 1)
        qh = (z1 * self.rho) >> (k + 1)
        r = (z - qh * self.p) & self.mask3          # limb arithmetic wraps
        if not (0 <= z - qh * self.p < 3 * self.p):
            self.good_reductions = False
        if r >= self.p: r = (r - self.p) & self.mask3
        if r >= self.p: r = (r - self.p) & self.mask3
        return r
    def h(self, x):
        x2 = self.red(x * x)
        t = self.red((self.a * x2) & self.mask3)
        s = self.red((t + self.b * x + self.c) & self.mask3)
        return (s & ((1 << (self.w + 1)) - 1)) >> 1   # h' in [0, 2^w)
    def bkt(self, hp, e):
        return hp >> (self.w - e)

    # ---------------- layout ----------------
    def addr(self, kind, lev, ident, slot, off):
        # kind 0 = entries (slot 3*B^lev), 1 = directory (slot 2*B^lev), 2 = presence (slot B^lev)
        o = ident * slot + off
        if self.check_layout and o >= (1 << self.RS):
            raise Violation("region overflow kind %d level %d offset %d >= 2^%d" % (kind, lev, o, self.RS))
        return (3 * lev + kind) * (1 << self.RS) + o
    def E(self, lev, ident, i, f):
        return self.addr(0, lev, ident, 3 * self.B ** lev, 3 * i + f)
    def D(self, lev, ident, cb, f):
        return self.addr(1, lev, ident, 2 * self.B ** lev, 2 * cb + f)
    def P(self, lev, ident, wi):
        return self.addr(2, lev, ident, self.B ** lev, wi)

    def bitscan(self, u):
        t = u & (-u)
        return self.m.load(self.tab + t)

    # ---------------- update ----------------
    def update(self, x, v):
        B, beta, w = self.B, self.beta, self.w
        u = self.U
        hp = self.h(x)
        self.m.write(self.E(0, u, 0, 0), hp); self.m.write(self.E(0, u, 0, 1), x); self.m.write(self.E(0, u, 0, 2), v)
        r = u % B
        old = self.m.load(self.P(0, u - 1, 0)) if r != 0 else 0
        f = self.bkt(hp, beta)
        self.m.write(self.P(0, u, 0), old | (1 << (f * B + (B - 1 - r))))
        self.U = u + 1
        lev, ident = 0, u
        while ident % B == B - 1:
            G = ident // B
            self.merge(lev + 1, G)
            lev, ident = lev + 1, G

    def merge(self, lev, G):
        B, beta, w = self.B, self.beta, self.w
        N = B ** lev
        e_out = lev * beta          # output coarse exponent = input fine exponent
        e_in_c = (lev - 1) * beta   # input coarse exponent
        e_out_f = (lev + 1) * beta  # output fine exponent
        in_ver = G * B + (B - 1)
        rnew = G % B
        out_i = 0
        word = None
        for bb in range(N):
            if bb & (B - 1) == 0:
                word = self.m.load(self.P(lev - 1, in_ver, bb >> beta))
            vec = (word >> ((bb & (B - 1)) * B)) & ((1 << B) - 1)
            flagged = []
            u = vec
            while u:
                t = u & (-u)
                pos = self.m.load(self.tab + t)
                flagged.append(B - 1 - pos)
                u &= u - 1
            # the bit scans above are charged once per round below; undo this pass's count
            self.m.loads -= len(flagged)
            start = out_i
            acc = self.m.load(self.P(lev, G - 1, bb)) if rnew != 0 else 0
            last = None
            cb = bb >> beta
            while True:
                best = None
                for r in flagged:
                    self.m.loads += 1   # one table load per bit scan per round
                    rid = G * B + r
                    if lev - 1 == 0:
                        hpe = self.m.load(self.E(0, rid, 0, 0)); xe = self.m.load(self.E(0, rid, 0, 1))
                        key = (hpe, xe)
                        cand = (key, r, 0) if (last is None or key > last) else None
                    else:
                        s = self.m.load(self.D(lev - 1, rid, cb, 0)); e = self.m.load(self.D(lev - 1, rid, cb, 1))
                        cand = None
                        i = s
                        while i < e:
                            hpe = self.m.load(self.E(lev - 1, rid, i, 0)); xe = self.m.load(self.E(lev - 1, rid, i, 1))
                            bk = self.bkt(hpe, e_out)
                            if bk < bb:
                                i += 1; continue
                            if bk > bb:
                                break
                            key = (hpe, xe)
                            if last is not None and key <= last:
                                i += 1; continue
                            cand = (key, r, i); break
                    if cand is not None:
                        if best is None or cand[0] < best[0] or (cand[0] == best[0] and cand[1] > best[1]):
                            best = cand
                if best is None:
                    break
                key, r, i = best
                rid = G * B + r
                vv = self.m.load(self.E(lev - 1, rid, i, 2))
                self.m.write(self.E(lev, G, out_i, 0), key[0]); self.m.write(self.E(lev, G, out_i, 1), key[1]); self.m.write(self.E(lev, G, out_i, 2), vv)
                out_i += 1
                last = key
                f = self.bkt(key[0], e_out_f)
                acc |= 1 << ((f & (B - 1)) * B + (B - 1 - rnew))
            self.m.write(self.D(lev, G, bb, 0), start); self.m.write(self.D(lev, G, bb, 1), out_i)
            self.m.write(self.P(lev, G, bb), acc)

    # ---------------- read ----------------
    def read(self, q):
        B, beta, w = self.B, self.beta, self.w
        hq = self.h(q)
        Q = (hq, q)
        U = self.U
        lev = 0
        while B ** lev <= U:
            d = (U // B ** lev) % B
            if d != 0:
                ver = U // B ** lev - 1
                cbq = self.bkt(hq, lev * beta)
                fq = self.bkt(hq, (lev + 1) * beta)
                word = self.m.load(self.P(lev, ver, cbq))
                vec = (word >> ((fq & (B - 1)) * B)) & ((1 << B) - 1)
                u = vec
                while u:   # lowest set bit = newest run
                    pos = self.bitscan(u)
                    u &= u - 1
                    r = B - 1 - pos
                    rid = (U // B ** (lev + 1)) * B + r
                    if lev == 0:
                        hpe = self.m.load(self.E(0, rid, 0, 0)); xe = self.m.load(self.E(0, rid, 0, 1))
                        if (hpe, xe) == Q:
                            return self.m.load(self.E(0, rid, 0, 2))
                    else:
                        s = self.m.load(self.D(lev, rid, cbq, 0)); e = self.m.load(self.D(lev, rid, cbq, 1))
                        i = s
                        while i < e:
                            hpe = self.m.load(self.E(lev, rid, i, 0)); xe = self.m.load(self.E(lev, rid, i, 1))
                            if (hpe, xe) >= Q:
                                if (hpe, xe) == Q:
                                    return self.m.load(self.E(lev, rid, i, 2))
                                break
                            i += 1
            lev += 1
        return 0

def good_seed(w, rng, p=None):
    if p is None:
        p = nextprime(1 << w)
    assert (1 << w) < p < (1 << (w + 1)) and isprime(p)
    rho = (4 ** (w + 1)) // p
    return (p, rho, rng.randrange(p), rng.randrange(p), rng.randrange(p))

def sequence(name, n, w, rng):
    # returns a list of ops ('u', x, v) or ('r', q); fixed before the seed (rng is the sequence generator)
    ops = []
    half = n // 2
    W = 1 << w
    if name == 'uni':
        for t in range(half):
            ops.append(('u', rng.randrange(W), t + 1)); ops.append(('r', rng.randrange(W)))
    elif name == 'rep':        # the same K addresses updated cyclically; reads of absent addresses inside the progression
        K = max(1, int(math.isqrt(half)))
        base = 1 << (w // 2)
        for t in range(half):
            ops.append(('u', base + 2 * (t % K), t + 1)); ops.append(('r', base + 2 * rng.randrange(K) + 1))
    elif name == 'ap':         # long progression with stride 2^(w/2), reads absent in the middle
        D = 1 << (w // 2)
        for t in range(half):
            ops.append(('u', (t * D) % W, t + 1)); ops.append(('r', (rng.randrange(half) * D + D // 2) % W))
    elif name == 'cons':       # consecutive addresses; reads mix present and absent
        for t in range(half):
            ops.append(('u', t, t + 1)); ops.append(('r', rng.randrange(2 * half)))
    elif name == 'hot':        # one hot address in every window, rest fresh; reads of the hot address and of absent ones
        for t in range(half):
            x = 7 if t % 2 == 0 else 1000 + t
            ops.append(('u', x, t + 1)); ops.append(('r', 7 if t % 3 == 0 else (1 << (w - 1)) + t))
    elif name == 'absent':     # every read misses: visits every level
        for t in range(half):
            ops.append(('u', 2 * t, t + 1)); ops.append(('r', 2 * rng.randrange(half) + 1))
    else:
        raise ValueError(name)
    return ops

def run(ops, w, beta, seed, check_layout=True):
    S = Z1plus(w, beta, seed, check_layout)
    ref = {}
    errors = 0
    for op in ops:
        if op[0] == 'u':
            S.update(op[1], op[2]); ref[op[1]] = op[2]
        else:
            got = S.read(op[1])
            if got != ref.get(op[1], 0):
                errors += 1
    probes = S.m.loads + S.m.writes
    return probes, errors, S.init_probes, S.good_reductions

def main(argv):
    """Run one mode; return the number of problems found."""
    mode = argv[0]
    sys.argv = [sys.argv[0]] + list(argv)
    bad_count = 0
    if mode == 'cost':
        # cost  W BETA N SEEDS FAMILIES
        w, beta, n, seeds = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
        fams = sys.argv[6].split(',')
        B = 1 << beta
        Lb = 0
        while B ** (Lb + 1) <= n: Lb += 1
        bound = 75 * n * (Lb + 1)
        for fam in fams:
            ops = sequence(fam, n, w, random.Random(5))
            rng = random.Random(1000 + beta)
            vals = []
            for s in range(seeds):
                pr, err, initp, good = run(ops, w, beta, good_seed(w, rng))
                assert err == 0 and good, (fam, s, err, good)
                vals.append(pr)
            mean = sum(vals) / len(vals)
            print("cost w=%d B=%d n=%d fam=%-6s seeds=%d  probes/op mean %.2f max %.2f | per op per level %.2f | bound 75(L+1)=%d per op | ratio mean/bound %.3f | init %d"
                  % (w, B, n, fam, seeds, mean / n, max(vals) / n, mean / n / (Lb + 1), 75 * (Lb + 1), mean / bound, initp), flush=True)
    elif mode == 'bad':
        # bad  W BETA N : bad seeds must stay legal and correct
        w, beta, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        p = nextprime(1 << w)
        rho = (4 ** (w + 1)) // p
        bads = {
            'const_hash(a=b=0)': (p, rho, 0, 0, 12345),
            'composite_p': ((1 << w) + 2, (4 ** (w + 1)) // ((1 << w) + 2), 3, 5, 7),
            'wrong_rho': (p, rho + 12345, 98765, 4321, 77),
            'rho_zero': (p, 0, 98765, 4321, 77),
            'p_zero': (0, 0, 98765, 4321, 77),
            'huge_coeffs': ((1 << (w + 2)) - 1, (1 << (w + 2)) - 1, (1 << (w + 2)) - 1, (1 << (w + 2)) - 1, (1 << (w + 2)) - 1),
        }
        for fam in ['uni', 'rep', 'ap', 'cons', 'hot', 'absent']:
            ops = sequence(fam, n, w, random.Random(5))
            for name, sd in bads.items():
                try:
                    pr, err, _, good = run(ops, w, beta, sd)
                    print("bad-seed %-18s fam=%-6s probes/op %.2f read errors %d  (Barrett in range: %s)" % (name, fam, pr / n, err, good), flush=True)
                    bad_count += err != 0
                except Violation as ex:
                    print("bad-seed %-18s fam=%-6s W-VIOLATION %s" % (name, fam, ex), flush=True)
                    bad_count += 1
    elif mode == 'neg':
        # negative control: a scheme variant that ignores the directory end bound must hit an unwritten cell
        w, beta, n = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        ops = sequence('uni', n, w, random.Random(5))
        S = Z1plus(w, beta, good_seed(w, random.Random(3)))
        try:
            for op in ops:
                if op[0] == 'u': S.update(op[1], op[2])
            # load one past the end of the newest run at the top level
            lev = 1
            while S.B ** (lev + 1) <= S.U: lev += 1
            ident = S.U // S.B ** lev - 1
            cnt = S.m.load(S.D(lev, ident, S.B ** lev - 1, 1))
            S.m.load(S.E(lev, ident, cnt, 0))
            print("negative control: no violation (unexpected)")
            bad_count += 1
        except Violation as ex:
            print("negative control: W-VIOLATION %s" % ex)
        try:
            S.m.write(S.D(1, 0, 0, 0), 0)
            print("negative control 2: no violation (unexpected)")
            bad_count += 1
        except Violation as ex:
            print("negative control 2: W-VIOLATION %s" % ex)
    return bad_count


DEFAULT = [['cost', '32', '2', '2048', '2', 'uni,rep,ap,cons,hot,absent'], ['bad', '32', '2', '1024'], ['neg', '32', '2', '2048']]

if __name__ == '__main__':
    if len(sys.argv) > 1:
        sys.exit(1 if main(sys.argv[1:]) else 0)
    problems = 0
    for args in DEFAULT:
        print('$ ' + ' '.join(args), flush=True)
        problems += main(args)
    print('default suite: problems %d' % problems)
    sys.exit(1 if problems else 0)
