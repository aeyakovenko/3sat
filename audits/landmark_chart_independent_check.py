#!/usr/bin/env python3
"""Independent checker for the landmark shared-bank degree-0 chart of the seed
note's runs, written during review as a cross-check of
landmark_shared_bank_chart_check.py.

It shares no code with that script, except that modes compare and mut-reviewed
load its evaluator to test it.  The file generators are the journal audit's own
(seed_chart_forced_memory_audit.py).

Run: python3 landmark_chart_independent_check.py [smoke | exhaustive | m8 | compare | mut-independent | mut-reviewed]
Without an argument it runs the smoke test (the exhaustive check at m = 2 and 4).

Model (from the chart note, re-implemented here):
  registers I A V T U M H and pc; memory words at every address 0..2^W-1;
  W = max(bitlen(m+1), bitlen(|program|), 2); input read IN r <- f(reg).
Chart: cuts at time 0, at loop heads with global counter G = 0, g, 2g, ... < 2m,
and at the accepting halt.  Row k is given by an evaluator that sees only
(k, coordinate, file bytes, bank bits).  The check: row 0 equals the all-zero
configuration at EVERY coordinate (all 2^W addresses); every gap is replayed
from row k (entry reads through the evaluator, private overlay of stores) and
the exit is compared with row k+1 at EVERY coordinate; the last row's pc is the
accepting halt.  Separately: every row equals the directly simulated snapshot.
"""
import sys, os, random
sys.dont_write_bytecode = True   # importing the journal audit leaves no __pycache__
from collections import Counter
from itertools import permutations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from seed_chart_forced_memory_audit import pinned_file, missing_file   # the journal audit's generators

REGS = ('I', 'A', 'V', 'T', 'U', 'M', 'H')

# ------------------------------------------------------------------ independent machine
def build(family):
    code, lab, fix = [], {}, []
    def op(*a):
        code.append(list(a))
    op('len', 'M'); op('half', 'H', 'M'); op('set', 'I', 0)
    lab['h1'] = len(code)
    op('jge', 'I', 'M', '@p2init')
    op('in', 'A', 'I')
    if family == 'main':
        op('ld', 'V', 'A'); op('jz', 'V', '@store')
        op('sub1', 'T', 'V'); op('lt', 'T', 'T', 'H'); op('lt', 'U', 'I', 'H')
        op('jeq', 'T', 'U', '@fb')
    lab['store'] = len(code)
    op('inc', 'T', 'I'); op('st', 'A', 'T'); op('inc', 'I', 'I'); op('jmp', '@h1')
    lab['p2init'] = len(code)
    op('set', 'I', 0)
    lab['h2'] = len(code)
    op('jge', 'I', 'M', '@acc'); op('ld', 'V', 'I'); op('jz', 'V', '@rej')
    op('jgt', 'V', 'M', '@rej'); op('sub1', 'T', 'V'); op('in', 'U', 'T')
    op('jne', 'U', 'I', '@rej'); op('inc', 'I', 'I'); op('jmp', '@h2')
    lab['acc'] = len(code); op('halt')
    lab['rej'] = len(code); op('halt')
    lab['fb'] = len(code); op('halt')
    for ins in code:
        for i, a in enumerate(ins):
            if isinstance(a, str) and a.startswith('@'):
                ins[i] = lab[a[1:]]
    return [tuple(x) for x in code], lab


def wordwidth(m, code):
    return max((m + 1).bit_length(), len(code).bit_length(), 2)


def run_step(code, get, put, fvals, m, W):
    """One instruction. get/put take keys ('pc',), ('r',name), ('m',addr)."""
    mask = (1 << W) - 1
    pc = get(('pc',))
    if pc >= len(code) or code[pc][0] == 'halt':
        return
    ins = code[pc]; o = ins[0]; nxt = pc + 1
    r = lambda n: get(('r', n))
    if o == 'len':   put(('r', ins[1]), m & mask)
    elif o == 'half': put(('r', ins[1]), r(ins[2]) // 2)
    elif o == 'set':  put(('r', ins[1]), ins[2])
    elif o == 'inc':  put(('r', ins[1]), (r(ins[2]) + 1) & mask)
    elif o == 'sub1': put(('r', ins[1]), (r(ins[2]) - 1) & mask)
    elif o == 'lt':   put(('r', ins[1]), int(r(ins[2]) < r(ins[3])))
    elif o == 'in':
        j = r(ins[2]); put(('r', ins[1]), (fvals[j] if j < m else 0) & mask)
    elif o == 'ld':   put(('r', ins[1]), get(('m', r(ins[2]))))
    elif o == 'st':   put(('m', r(ins[1])), r(ins[2]))
    elif o == 'jge':  nxt = ins[3] if r(ins[1]) >= r(ins[2]) else nxt
    elif o == 'jgt':  nxt = ins[3] if r(ins[1]) > r(ins[2]) else nxt
    elif o == 'jeq':  nxt = ins[3] if r(ins[1]) == r(ins[2]) else nxt
    elif o == 'jne':  nxt = ins[3] if r(ins[1]) != r(ins[2]) else nxt
    elif o == 'jz':   nxt = ins[2] if r(ins[1]) == 0 else nxt
    elif o == 'jmp':  nxt = ins[1]
    else: raise ValueError(o)
    put(('pc',), nxt)


def all_coords(W):
    return [('pc',)] + [('r', x) for x in REGS] + [('m', a) for a in range(1 << W)]


def cut_times(m, g, family):
    """Derived by hand from this program text: 3 setup instructions; phase-1 body of
    8 (main) or 6 (first) instructions on a permutation; 2 instructions between the
    phases (final head test, reset of I); phase-2 body 9; final head test 1."""
    c1 = 8 if family == 'main' else 6
    t = [0]
    G = 0
    while G < 2 * m:
        t.append(3 + c1 * G if G < m else 3 + c1 * m + 2 + 9 * (G - m))
        G += g
    t.append(3 + c1 * m + 2 + 9 * m + 1)
    return t

# ------------------------------------------------------------------ bank
def cycles(f):
    m = len(f); seen = [False] * m; out = []
    for s in range(m):
        if not seen[s]:
            c = []; x = s
            while not seen[x]:
                seen[x] = True; c.append(x); x = f[x]
            out.append(c)
    return out


def make_bank(f, g, h):
    """6-bit width, then g, h, K, then K sorted (mark, preceding mark) pairs."""
    prev = {}
    for c in cycles(f):
        if len(c) > h:
            mk = [c[i] for i in range(0, len(c), h)]
            for i in range(len(mk)):
                prev[mk[i]] = mk[i - 1]
    K = len(prev)
    wb = max(1, max(len(f), g, h, K).bit_length())
    fld = lambda v: format(v, '0%db' % wb)
    s = format(wb, '06b') + fld(g) + fld(h) + fld(K)
    for mk in sorted(prev):
        s += fld(mk) + fld(prev[mk])
    return s, prev

# ------------------------------------------------------------------ independent evaluator
class MyEval:
    """Sees only the file bytes, the bank bits, and its fixed text (family, labels, W)."""
    def __init__(self, data, bank, family, lab, W):
        self.data, self.bank, self.family, self.lab, self.W = data, bank, family, lab, W
        self.memo = {}
        self.max_probes = 0
        self.probes = 0
        # header "p cnf V C\n"
        nl = data.index(b'\n')
        _, _, V, C = data[:nl].split()
        V, C = int(V), int(C)
        self.hlen = nl + 1
        self.D = len(str(V))
        self.rowlen = 3 * self.D + 8
        self.m = (C - 7) // 2 if family == 'main' else (C - 7) // 4
        self.unit0 = C - self.m           # unit rows are the last m rows
        # bank
        def fld(pos, w):
            s = bank[pos:pos + w]
            return int(s, 2) if w > 0 and len(s) == w else 0
        self.wb = wb = fld(0, 6)
        self.g, self.h, self.K = fld(6, wb), fld(6 + wb, wb), fld(6 + 2 * wb, wb)
        self.keys = [fld(6 + 3 * wb + 2 * wb * i, wb) for i in range(self.K)]
        self.vals = [fld(6 + 3 * wb + 2 * wb * i + wb, wb) for i in range(self.K)]

    def f(self, x):
        self.probes += 1
        if not (0 <= x < self.m):
            return 0
        base = self.hlen + (self.unit0 + x) * self.rowlen
        field = self.data[base:base + self.D + 1].decode()
        return int(field.strip().lstrip('-')) - 4

    def pred(self, x):
        # binary search exactly as a sorted directory would be searched
        lo, hi = 0, self.K
        while lo < hi:
            mid = (lo + hi) // 2
            if self.keys[mid] == x:
                return self.vals[mid]
            if self.keys[mid] < x:
                lo = mid + 1
            else:
                hi = mid
        return None

    def inv(self, y):
        if ('inv', y) in self.memo:
            return self.memo[('inv', y)]
        self.probes = 0
        cap = 2 * self.h + 2
        x, res = y, 0
        while True:
            p = self.pred(x)
            if p is not None:
                x = p
                while self.probes < cap:
                    z = self.f(x)
                    if z == y:
                        res = x; break
                    x = z
                break
            if self.probes >= cap:
                break
            z = self.f(x)
            if z == y:
                res = x; break
            x = z
        self.max_probes = max(self.max_probes, self.probes)
        self.memo[('inv', y)] = res
        return res

    def nrows(self):
        g = self.g
        return (-(-2 * self.m // g) if g > 0 else 0) + 2

    def word(self, k, c):
        key = (k, c)
        if key in self.memo:
            return self.memo[key]
        m, g, lab = self.m, self.g, self.lab
        n1 = -(-2 * m // g) if g > 0 else 0
        if k == 0 or k > n1 + 1:
            v = 0
        else:
            if k == n1 + 1:
                kind, y = 'halt', m
            else:
                G = (k - 1) * g
                kind, y = ('p1', G) if G < m else ('p2', G - m)
            if c == ('pc',):
                v = lab['h1'] if kind == 'p1' else lab['h2'] if kind == 'p2' else lab['acc']
            elif c[0] == 'r':
                n = c[1]
                if n == 'M': v = m
                elif n == 'H': v = m // 2
                elif kind == 'p1':
                    i = y
                    v = {'I': i, 'A': (self.f(i - 1) if i >= 1 else 0), 'V': 0, 'T': i, 'U': 0}[n]
                else:
                    if n == 'I': v = y
                    elif n == 'A': v = self.f(m - 1)
                    elif y == 0: v = {'V': 0, 'T': m, 'U': 0}[n]
                    elif n == 'U': v = y - 1
                    elif n == 'V': v = self.inv(y - 1) + 1
                    else: v = self.inv(y - 1)
            else:
                a = c[1]
                if 0 <= a < m:
                    j = self.inv(a)
                    v = (j + 1 if j < y else 0) if kind == 'p1' else j + 1
                else:
                    v = 0
        v &= (1 << self.W) - 1
        self.memo[key] = v
        return v


class TheirEvalAdapter:
    """Wraps the evaluator of landmark_shared_bank_chart_check.py so that this checker can test it."""
    def __init__(self, L, data, bank, family, W, hcap):
        self.L = L
        L.MASK[0] = (1 << W) - 1
        # hcap: the format parameter h_fmt of the reviewed evaluator, set to the honest h as its own checks do
        self.ev = L.Evaluator(data, bank, family, hcap)
        # Reset the probe counter: a first call may parse f before any decode.
        self.ev.probes = 0
        self.ev.c = 0; self.ev._header(); self.ev._bankhdr()
        self.g = self.ev.g
        self.max_probes = 0
    def word(self, k, c):
        x = ('pc',) if c == ('pc',) else c
        v = self.ev.word(k, x)[0]
        self.max_probes = self.ev.decode_probes_max
        return v

# ------------------------------------------------------------------ checker
def true_rows(code, f, family, times, W):
    m = len(f); st = {}
    get = lambda c: st.get(c, 0)
    def put(c, v):
        if v: st[c] = v
        else: st.pop(c, None)
    snaps, t = [], 0
    for tau in times:
        while t < tau:
            run_step(code, get, put, f, m, W); t += 1
        snaps.append(dict(st))
    return snaps


def check(code, lab, f, family, ev, W, g_sched, snaps=None):
    """Return (accept, rows_true)."""
    m = len(f)
    times = cut_times(m, g_sched, family)
    coords = all_coords(W)
    ok = all(ev.word(0, c) == 0 for c in coords)               # initial condition
    for k in range(len(times) - 1):
        entry, over = {}, {}
        def get(c):
            if c in over: return over[c]
            if c not in entry: entry[c] = ev.word(k, c)
            return entry[c]
        def put(c, v): over[c] = v
        for _ in range(times[k + 1] - times[k]):
            run_step(code, get, put, f, m, W)
        for c in coords:
            e = over[c] if c in over else entry[c] if c in entry else ev.word(k, c)
            if e != ev.word(k + 1, c):
                ok = False
    ok = ok and ev.word(len(times) - 1, ('pc',)) == lab['acc']   # terminal condition
    if snaps is None:
        snaps = true_rows(code, f, family, times, W)
    rows_true = all(ev.word(k, c) == snaps[k].get(c, 0)
                    for k in range(len(times)) for c in coords)
    return ok, rows_true, snaps


def genuine_heads_ok(code, lab, f, family, g, W):
    times = cut_times(len(f), g, family)
    snaps = true_rows(code, f, family, times, W)
    pcs = [s.get(('pc',), 0) for s in snaps]
    exp = [0] + [lab['h1'] if (i * g) < len(f) else lab['h2'] for i in range(len(times) - 2)] + [lab['acc']]
    return pcs == exp, snaps


def mkfile(f, fam):
    return pinned_file(list(f)) if fam == 'main' else missing_file(list(f))

# ------------------------------------------------------------------ modes
def mode_exhaustive(ms):
    tally = Counter(); worst = Counter()
    for m in ms:
        for fam in ('main', 'first'):
            code, lab = build(fam); W = wordwidth(m, code)
            for f in permutations(range(m)):
                data = mkfile(f, fam)
                for h in range(1, m + 1):
                    for g in range(1, m + 1):
                        okh, snaps = genuine_heads_ok(code, lab, f, fam, g, W)
                        assert okh, (m, fam, f, g)
                        bank, prev = make_bank(f, g, h)
                        K = len(prev)
                        assert K * h < 2 * m or K == 0
                        assert len(bank) == 6 + max(1, max(m, g, h, K).bit_length()) * (3 + 2 * K)
                        ev = MyEval(data, bank, fam, lab, W)
                        ok, rt, _ = check(code, lab, f, fam, ev, W, g, snaps)
                        assert ok and rt, (m, fam, f, h, g)
                        assert ev.max_probes <= h, (m, f, h, ev.max_probes)
                        tally[(m, fam)] += 1
                        worst[(m, fam, 'probes==h')] += (ev.max_probes == h)
    print('independent checker, all (h,g) in [1..m]^2, all permutations, all 2^W addresses:', dict(tally))
    print('  cases whose largest decode used exactly h probes:', dict(worst))


def mode_m8(sample=None, seed=1):
    m = 8; h = g = 2
    rng = random.Random(seed)
    perms = list(permutations(range(m)))
    if sample:
        perms = rng.sample(perms, sample)
    for fam in ('main', 'first'):
        code, lab = build(fam); W = wordwidth(m, code); n = 0; mb = 0
        for f in perms:
            data = mkfile(f, fam)
            okh, snaps = genuine_heads_ok(code, lab, f, fam, g, W); assert okh
            bank, prev = make_bank(f, g, h)
            ev = MyEval(data, bank, fam, lab, W)
            ok, rt, _ = check(code, lab, f, fam, ev, W, g, snaps)
            assert ok and rt and ev.max_probes <= h, (fam, f)
            n += 1; mb = max(mb, len(bank))
        print(f'm=8 h=g=2 {fam}: {n} permutations sound (independent checker, all {1<<W} addresses), max bank {mb} bits, W={W}')


def mode_compare(ms):
    """Compare this machine with the reviewed one step by step, and the two evaluators."""
    import landmark_shared_bank_chart_check as L
    n_steps = 0; n_words = 0
    for m in ms:
        for fam in ('main', 'first'):
            code, lab = build(fam); W = wordwidth(m, code)
            tprog, tlab = L.PROGS[fam]
            assert W == L.width(m, tprog), (m, fam)
            assert {k: lab[k] for k in ('h1', 'h2', 'acc')} == {'h1': tlab['P1'], 'h2': tlab['P2'], 'acc': tlab['ACCEPT']}
            for f in permutations(range(m)):
                # step-by-step trace equality
                mine, theirs = {}, L.TrueState()
                def put(c, v):
                    if v: mine[c] = v
                    else: mine.pop(c, None)
                tr = lambda d: {(('pc',) if k == ('pc',) else k): v for k, v in d.items()}
                for t in range(3 + 8 * m + 2 + 9 * m + 5):
                    run_step(code, lambda c: mine.get(c, 0), put, list(f), m, W)
                    L.step(tprog, theirs.read, theirs.write, list(f), m, (1 << W) - 1)
                    assert mine == tr(theirs.w), (m, fam, f, t)
                    n_steps += 1
                data = mkfile(f, fam)
                assert data == L.make_file(list(f), fam)
                for h in range(1, m + 1):
                    for g in range(1, m + 1):
                        bank, _ = make_bank(f, g, h)
                        assert bank == L.bank_for(f, g, h)
                        ev = MyEval(data, bank, fam, lab, W)
                        te = TheirEvalAdapter(L, data, bank, fam, W, h)
                        for k in range(ev.nrows()):
                            for c in all_coords(W):
                                assert ev.word(k, c) == te.word(k, c), (m, fam, f, h, g, k, c)
                                n_words += 1
    print(f'reviewed machine == independent machine at every step: {n_steps} steps; '
          f'reviewed evaluator == independent evaluator: {n_words} (row, coordinate) values; banks and files identical')


def corruptions(f, g, h, bank, prev):
    """Every single-bit flip; every wrong preceding mark; every dropped mark;
    every added (non-mark, pred) pair."""
    m = len(f)
    out = []
    for i in range(len(bank)):
        out.append(('flip', bank[:i] + ('1' if bank[i] == '0' else '0') + bank[i + 1:]))
    def enc(d):
        K = len(d); wb = max(1, max(m, g, h, K).bit_length())
        fld = lambda v: format(v, '0%db' % wb)
        return format(wb, '06b') + fld(g) + fld(h) + fld(K) + ''.join(fld(k) + fld(d[k]) for k in sorted(d))
    for mk in prev:
        for p in range(m):
            if p != prev[mk]:
                d = dict(prev); d[mk] = p; out.append(('pred', enc(d)))
        d = dict(prev); del d[mk]; out.append(('drop', enc(d)))
    for x in range(m):
        if x not in prev:
            for p in range(m):
                d = dict(prev); d[x] = p; out.append(('add', enc(d)))
    return out


def mode_mutation(ms, which, hg, perm_sample=None, seed=3):
    if which == 'reviewed':
        import landmark_shared_bank_chart_check as L
    rng = random.Random(seed)
    tally = Counter()
    for m in ms:
        for fam in ('main', 'first'):
            code, lab = build(fam); W = wordwidth(m, code)
            perms = list(permutations(range(m)))
            if perm_sample and len(perms) > perm_sample:
                perms = rng.sample(perms, perm_sample)
            for f in perms:
                data = mkfile(f, fam)
                pairs = hg if hg else [(h, g) for h in range(1, m + 1) for g in range(1, m + 1)]
                for (h, g) in pairs:
                    good, prev = make_bank(f, g, h)
                    for kind, bad in corruptions(f, g, h, good, prev):
                        if bad == good:
                            continue
                        if which == 'independent':
                            ev = MyEval(data, bad, fam, lab, W)
                            gs = ev.g if ev.g > 0 else 1
                        else:
                            ev = TheirEvalAdapter(L, data, bad, fam, W, h)
                            gs = ev.g if ev.g > 0 else 1
                        ok, rt, _ = check(code, lab, f, fam, ev, W, gs)
                        assert ok == rt, (which, m, fam, f, h, g, kind, bad)
                        tally[(kind, 'accepted' if ok else 'rejected')] += 1
    print(f'corruptions, evaluator={which}, m={ms}, (h,g)={hg or "all"}: checker accepts <=> all rows true:',
          dict(sorted(tally.items())), 'total', sum(tally.values()))


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'smoke'
    if mode == 'smoke':
        mode_exhaustive([2, 4])
    elif mode == 'exhaustive':
        mode_exhaustive([2, 4, 6])
    elif mode == 'm8':
        mode_m8(int(sys.argv[2]) if len(sys.argv) > 2 else None)
    elif mode == 'compare':
        mode_compare([2, 4, 6])
    elif mode == 'mut-independent':
        mode_mutation([4], 'independent', None)
        mode_mutation([6], 'independent', [(1, 1), (2, 2), (2, 1), (3, 2)], perm_sample=120)
    elif mode == 'mut-reviewed':
        mode_mutation([4], 'reviewed', None)
        mode_mutation([6], 'reviewed', [(1, 1), (2, 2), (2, 1), (3, 2)], perm_sample=120)
    else:
        sys.exit('usage: python3 landmark_chart_independent_check.py [smoke | exhaustive | m8 | compare | mut-independent | mut-reviewed]')
