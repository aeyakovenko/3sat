#!/usr/bin/env python3
"""Independent model-W simulator for the packed-presence-table array of
notes/packed-presence-tables-for-a-word-write-once-array.md, written during review from the note's
description of the scheme (after reading write_once_array_presence_table_simulator.cpp, so it is a second
implementation, not a blind one).

Memory: abstract cells named by tuples (kind, level, id, offset); a cell may be written once and may be
loaded only after it is written (both checked; a violation raises WViolation).  Every load and write is
counted by (op, level, category).  Scheme state between operations: the update counter U only.
Presence words hold P fields of B bits (w = P*B >= B^2); one presence word = one cell = one probe.
Bit scans cost one 'tab' probe each (the note's accounting); option --freescan makes them free.

Run from audits/:
  python3 write_once_array_presence_table_independent_simulator.py
      the default suite, about 10 s: the random workload at m = 2^12 (B = 8, two seeds, and once with the
      integer address layout), the five structured workloads at m = 2^10 (B = 4), and four negative
      controls that must abort; exits 1 if a run errs or a control does not abort.
  python3 write_once_array_presence_table_independent_simulator.py MU BETA P NU SEED [workload] [variant] [--intaddr] [--freescan]
      one run: m = 2^MU, B = 2^BETA, P fields per presence word, NU updates each followed by a read.
  workload: uniform (the random workload), samekey, seq, lowrange, fewkeys, mixed
  variant : ok | noend | noend1 (levels >= 1 only) (read ignores the directory end bound: must load an unwritten cell)
               | inplace (presence table updated in place at one address per level: must write twice)
               | tailload (a read loads the last slot of a deduplicated run at level >= 2: must load an unwritten cell)
               | dirtwice (one level-2 directory cell written twice: must write twice)
Nothing is written.
"""
import sys, random
from collections import defaultdict

class WViolation(Exception):
    pass

class Mem:
    KIND = {'K': 0, 'V': 1, 'D': 2, 'P': 3}
    def __init__(self):
        self.RS = None          # set to use the note's integer layout instead of tuple cells
        self.slot = None        # callback (kind, level) -> slot size
        self.c = {}
        self.op = 'init'
        self.cnt = defaultdict(int)   # (op, level, cat, 'L'|'W') -> count
    def addr(self, a, writing):
        if self.RS is None:
            return a
        kind, l, rid, off = a
        sl = self.slot(kind, l)
        if writing:
            assert off < sl, ('write outside slot', a, sl)
        x = ((4 * l + self.KIND[kind] + 1) << self.RS) + rid * sl + off
        assert rid * sl + off < (1 << self.RS), ('region overflow', a)
        return x
    def load(self, a, lev, cat):
        a = self.addr(a, False)
        if a not in self.c:
            raise WViolation(f'load of unwritten cell {a} during {self.op}')
        self.cnt[(self.op, lev, cat, 'L')] += 1
        return self.c[a]
    def write(self, a, v, lev, cat):
        a = self.addr(a, True)
        if a in self.c:
            raise WViolation(f'second write of cell {a} during {self.op}')
        self.cnt[(self.op, lev, cat, 'W')] += 1
        self.c[a] = v

class Z1:
    def __init__(self, mu, beta, P, variant='ok', freescan=False):
        self.mu, self.beta, self.B, self.P = mu, beta, 1 << beta, P
        assert P >= self.B and P & (P - 1) == 0
        self.M = Mem()
        self.U = 0            # the only state kept between operations
        self.variant = variant
        self.freescan = freescan
        self.stats = defaultdict(int)
    # granularities
    def ec(self, l): return min(l * self.beta, self.mu)
    def ef(self, l): return min((l + 1) * self.beta, self.mu)
    def coarse(self, x, l): return x >> (self.mu - self.ec(l))
    def fine(self, x, l): return x >> (self.mu - self.ef(l))
    def nwords(self, l): return max(1, (1 << self.ef(l)) // self.P)
    # field f of a presence word value
    def field(self, word, j): return (word >> (j * self.B)) & ((1 << self.B) - 1)
    def scan_cost(self, lev):
        if not self.freescan:
            self.M.cnt[(self.M.op, lev, 'tab', 'L')] += 1
    def pres_addr(self, l, ver, wi):
        if self.variant == 'inplace':
            return ('P', l, 0, wi)          # one mutable table per level (the natural RAM design)
        return ('P', l, ver, wi)

    def update(self, i, v):
        M = self.M; M.op = 'upd'
        u = self.U
        M.write(('K', 0, u, 0), i, 0, 'key')
        M.write(('V', 0, u, 0), v, 0, 'val')
        k = u % self.B
        fi = self.fine(i, 0)
        for wi in range(self.nwords(0)):
            acc = M.load(self.pres_addr(0, u - 1, wi), 0, 'pres') if k > 0 else 0
            if fi // self.P == wi:
                acc |= 1 << ((fi % self.P) * self.B + k)
            M.write(self.pres_addr(0, u, wi), acc, 0, 'pres')
        g, l = u, 0
        while g % self.B == self.B - 1:
            g //= self.B; l += 1
            self.merge(l, g)
        self.U = u + 1

    def run_bounds(self, l, rid, cb, lev):
        """(start, end) of coarse bucket cb in run rid of level l; level-0 runs hold one key at offset 0."""
        if l == 0:
            return 0, 1
        s, e = self.M.load(('D', l, rid, cb), lev, 'dir')
        return s, e

    def merge(self, l, g):
        M = self.M; B = self.B; P = self.P
        il = l - 1
        G0 = g * B
        k = g % B
        in_ver = G0 + B - 1
        ncb = 1 << self.ec(l)
        sub = 1 << (self.ef(l) - self.ec(l))       # fine buckets per output coarse bucket
        shift_in = self.ec(l) - self.ec(il)        # output coarse bucket -> input coarse bucket
        pos = 0
        cur_wi, acc = None, 0
        in_wi, in_word = None, 0
        self.stats[('merges', l)] += 1
        for b in range(ncb):
            # input presence field for b (input fine granularity == output coarse granularity)
            wiI = b // P
            if wiI != in_wi:
                in_word = M.load(self.pres_addr(il, in_ver, wiI), l, 'pres'); in_wi = wiI
            V = self.field(in_word, b % P)
            wi = (b * sub) // P
            if wi != cur_wi:
                if cur_wi is not None:
                    M.write(self.pres_addr(l, g, cur_wi), acc, l, 'pres')
                cur_wi = wi
                acc = M.load(self.pres_addr(l, g - 1, wi), l, 'pres') if k > 0 else 0
            start = pos
            last = -1
            if V:
                while True:
                    self.stats[('rounds', l)] += 1
                    best, best_r, best_p = None, None, None
                    W = V
                    while W:
                        self.scan_cost(l)
                        r = (W & -W).bit_length() - 1      # lsb
                        W &= W - 1
                        rid = G0 + r
                        s, e = self.run_bounds(il, rid, b >> shift_in, l)
                        p = s
                        while p < e:
                            x = M.load(('K', il, rid, p), l, 'key')
                            self.stats[('mkeys', l)] += 1
                            xb = self.coarse(x, l)
                            if xb < b or (xb == b and x <= last):
                                p += 1; continue
                            if xb == b and (best is None or x < best or (x == best and r > best_r)):
                                best, best_r, best_p = x, r, p
                            break
                    if best is None:
                        break
                    val = M.load(('V', il, G0 + best_r, best_p), l, 'val')
                    M.write(('K', l, g, pos), best, l, 'key')
                    M.write(('V', l, g, pos), val, l, 'val')
                    pos += 1
                    f = self.fine(best, l)
                    acc |= 1 << ((f % P) * B + k)
                    last = best
            M.write(('D', l, g, b), (start, pos), l, 'dir')
            if self.variant == 'dirtwice' and l == 2 and b == 0:
                M.write(('D', l, g, b), (start, pos), l, 'dir')                  # rewrite one directory cell
        M.write(self.pres_addr(l, g, cur_wi), acc, l, 'pres')
        self.stats[('mout', l)] += pos

    def read(self, q):
        M = self.M; M.op = 'read'; B = self.B
        U = self.U
        l = 0
        while B ** l <= U:
            d = (U // B ** l) % B
            if d:
                self.stats[('rlev', l)] += 1
                ver = U // B ** l - 1
                f = self.fine(q, l)
                word = M.load(self.pres_addr(l, ver, f // self.P), l, 'pres')
                V = self.field(word, f % self.P)
                G0 = (U // B ** (l + 1)) * B
                while V:
                    self.scan_cost(l)
                    r = V.bit_length() - 1              # msb: newest run first
                    V &= ~(1 << r)
                    self.stats[('flag', l)] += 1
                    rid = G0 + r
                    cb = self.coarse(q, l)
                    s, e = self.run_bounds(l, rid, cb, l)
                    if self.variant == 'tailload' and l >= 2:
                        M.load(('K', l, rid, (1 << self.ec(l)) - 1), l, 'key')   # last slot of the run's allocation
                    if self.variant == 'noend' or (self.variant == 'noend1' and l >= 1):
                        e = 1 << 62                      # forget the end bound: scan until key > q
                    p = s
                    while p < e:
                        x = M.load(('K', l, rid, p), l, 'key')
                        if x == q:
                            return M.load(('V', l, rid, p), l, 'val')
                        if x > q:
                            break
                        p += 1
            l += 1
        return 0

def gen(workload, mu, nu, rng):
    m = 1 << mu
    for s in range(nu):
        i, v, q = rng.randrange(m), rng.getrandbits(32), rng.randrange(m)
        if workload == 'samekey': i = 5 % m
        elif workload == 'seq': i = s % m
        elif workload == 'lowrange': i, q = i % max(1, m >> 6), q % max(1, m >> 6)
        elif workload == 'fewkeys': i, q = rng.randrange(3), rng.randrange(4)
        elif workload == 'mixed':
            i = [rng.randrange(m), s % m, 0, m - 1, (s * 7919) % m][s % 5]
        yield i, v, q

def run_one(a):
    flags = [x for x in a if x.startswith('--')]
    a = [x for x in a if not x.startswith('--')]
    mu, beta, P, nu, seed = map(int, a[:5])
    workload = a[5] if len(a) > 5 else 'uniform'
    variant = a[6] if len(a) > 6 else 'ok'
    rng = random.Random(seed)
    S = Z1(mu, beta, P, variant, freescan='--freescan' in flags)
    if '--intaddr' in flags:
        S.M.RS = max(8, (2 * nu + (1 << mu)).bit_length() + 1)
        S.M.slot = lambda kind, l: S.nwords(l) if kind == 'P' else (1 << S.ec(l))
    ref = {}
    errors = 0
    half = nu // 2
    snap = None; snapst = None
    try:
        for s, (i, v, q) in enumerate(gen(workload, mu, nu, rng)):
            if s == half:
                snap = dict(S.M.cnt); snapst = dict(S.stats)
            S.update(i, v); ref[i] = v
            if S.read(q) != ref.get(q, 0):
                errors += 1
    except WViolation as ex:
        print(f'W-VIOLATION ({variant}, {workload}): {ex}')
        return 3
    W = nu - half
    def d(key):
        return S.M.cnt.get(key, 0) - snap.get(key, 0)
    def ds(key):
        return S.stats.get(key, 0) - snapst.get(key, 0)
    levels = sorted({k[1] for k in S.M.cnt})
    print(f'mu={mu} B={S.B} P={P} nu={nu} seed={seed} workload={workload} variant={variant} freescan={"--freescan" in flags}')
    print('lev  upd(L+W)/upd  rd/read  flag/readlev  rounds/out  mkeys/out  out/upd')
    totU = totR = 0.0
    for l in levels:
        up = sum(d(k) for k in S.M.cnt if k[0] == 'upd' and k[1] == l) / W
        rd = sum(d(k) for k in S.M.cnt if k[0] == 'read' and k[1] == l) / W
        totU += up; totR += rd
        rl = ds(('rlev', l)); mo = ds(('mout', l))
        print(f'{l:3d}  {up:10.3f}  {rd:8.3f}  {ds(("flag", l)) / rl if rl else 0:10.3f}  '
              f'{ds(("rounds", l)) / mo if mo else 0:9.3f}  {ds(("mkeys", l)) / mo if mo else 0:9.3f}  {mo / W:7.3f}')
    allops = sum(S.M.cnt[k] for k in S.M.cnt if k[0] in ('upd', 'read'))
    print(f'TOTAL second half: per update {totU:.3f}  per read {totR:.3f}  per op {(totU + totR) / 2:.3f}')
    print(f'amortized from the start (all {2 * nu} ops): per op {allops / (2 * nu):.3f}')
    print(f'cells written {len(S.M.c)}  read errors {errors}  W-violations 0')
    return 5 if errors else 0

DEFAULT = ([['12', '3', '8', '8192', str(s)] for s in (1, 2)] + [['12', '3', '8', '8192', '1', 'uniform', 'ok', '--intaddr']]
           + [['10', '2', '4', '4096', '7', w] for w in ('samekey', 'seq', 'lowrange', 'fewkeys', 'mixed')])
NEGATIVE = [['12', '3', '8', '8192', '3', 'uniform', v] for v in ('inplace', 'noend1')] \
    + [['12', '3', '8', '8192', '1', 'uniform', v, '--intaddr'] for v in ('tailload', 'dirtwice')]

def main():
    a = sys.argv[1:]
    if a:
        sys.exit(run_one(a))
    bad = 0
    for args in DEFAULT:
        print('$ ' + ' '.join(args))
        bad += run_one(args) != 0
    for args in NEGATIVE:
        print('$ ' + ' '.join(args) + '   (negative control: must abort)')
        bad += run_one(args) != 3
    print(f'default suite: {len(DEFAULT)} runs and {len(NEGATIVE)} negative controls, problems: {bad}')
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
