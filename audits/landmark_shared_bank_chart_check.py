#!/usr/bin/env python3
"""The cycle-landmark shared-bank degree-0 chart for the program P of the seed note
(checking-an-interval-against-a-seed-of-unknown-bits.md).

Run: python3 landmark_shared_bank_chart_check.py [smoke | exhaustive | mutation | scale M ... | scale1 M ...]
Without an argument it runs the smoke test (the exhaustive check at m = 2 and 4, a few seconds).

Machine.  A register machine with indirect LOAD/STORE, run at instruction level for the
two loops of P.  The DIMACS field parse is abstracted as one input read INP (input reads
are constants in the chart format, so they cost no entry bits).  Two programs:
  P_main  : main family (2m+7 clauses), phase-1 same-half check with fallback exit,
            accepting halt = SAT verdict on permutation files;
  P_first : first family (4m+7 clauses), no check, accepting halt = UNSAT signal.

Chart.  Degree 0 (constant rows).  Cuts: time 0, every g-th loop head (global loop
counter G = 0, g, 2g, ... < 2m), and the halt.  The rows are given by one evaluator
program that sees only (row index, coordinate, file bytes, bank bit string); it reads
file bytes and bank fields through counters.  The bank: 6-bit width wb, then g, h, K,
then K sorted pairs (mark, preceding mark) of the cycle-landmark directory.

Checker.  For every gap: replay with a private overlay, fetching every entry word from
row k bit by bit (W evaluator calls per word), then compare every coordinate of the exit
with row k+1 (all registers, pc, B[0..m-1], guard addresses, and every address touched).
Initial condition: row 0 equals the true initial configuration on the same universe.
Terminal condition: last row's pc is the accepting halt.  Cross-check: every row equals
the direct simulation's snapshot; for corrupted banks, checker verdict == "all rows true".
"""
import sys, math, random
from itertools import permutations

# ---------------------------------------------------------------- files
# Copied (logic unchanged) from audits/seed_chart_forced_memory_audit.py of the journal.

def pinned_file(f):
    m = len(f)
    v = m + 3
    digits = len(str(v))
    rows = [tuple(-j if bits >> (j - 1) & 1 else j for j in (1, 2, 3)) for bits in range(1, 8)]
    rows += [(-1, 4 + j, 2) for j in range(m)]
    rows += [((4 + y) if i < m // 2 else -(4 + y), 1, 2) for i, y in enumerate(f)]
    text = f"p cnf {v} {len(rows)}\n" + "".join(
        " ".join(f"{lit:>{digits + 1}}" for lit in row) + " 0\n" for row in rows)
    data = text.encode("ascii")
    assert len(data) == 8 + digits + len(str(2 * m + 7)) + (2 * m + 7) * (3 * digits + 8)
    return data


def missing_file(f):
    m = len(f)
    x = lambda j: 4 + j
    prefix = lambda j: 4 + m + j
    v = 2 * m + 3
    digits = len(str(v))
    rows = [tuple(-j if bits >> (j - 1) & 1 else j for j in (1, 2, 3)) for bits in range(1, 8)]
    rows += [(-prefix(0), x(0), 1), (prefix(0), -x(0), 1)]
    for j in range(1, m):
        rows += [(-prefix(j - 1), prefix(j), 1), (-x(j), prefix(j), 1),
                 (prefix(j - 1), x(j), -prefix(j))]
    rows.append((prefix(m - 1), 1, 2))
    rows += [(-x(y), 1, 2) for y in f]
    text = f"p cnf {v} {len(rows)}\n" + "".join(
        " ".join(f"{lit:>{digits + 1}}" for lit in row) + " 0\n" for row in rows)
    data = text.encode("ascii")
    assert len(rows) == 4 * m + 7
    assert len(data) == 8 + digits + len(str(4 * m + 7)) + (4 * m + 7) * (3 * digits + 8)
    return data

# ---------------------------------------------------------------- machine

PC = ('pc',)
REGS = ['I', 'A', 'V', 'T', 'U', 'M', 'H']
R = {r: ('r', r) for r in REGS}

def program(family):
    """Return (prog, labels).  Jump targets are absolute instruction indices."""
    P = []
    lab = {}
    P += [('LEN', 'M'), ('SHR', 'H', 'M'), ('SETI', 'I', 0)]
    lab['P1'] = len(P)
    P.append(('JGE', 'I', 'M', 'P2INIT'))
    P.append(('INP', 'A', 'I'))                    # A <- f(I)
    if family == 'main':
        P.append(('LOAD', 'V', 'A'))               # V <- B[A]
        P.append(('JZ', 'V', 'STEP'))
        P.append(('SUBI', 'T', 'V', 1))
        P.append(('LT', 'T', 'T', 'H'))            # T <- (V-1 < m/2)
        P.append(('LT', 'U', 'I', 'H'))            # U <- (I < m/2)
        P.append(('JEQ', 'T', 'U', 'FALLBACK'))
    lab['STEP'] = len(P)
    P.append(('ADDI', 'T', 'I', 1))
    P.append(('STORE', 'A', 'T'))                  # B[A] <- I+1
    P.append(('ADDI', 'I', 'I', 1))
    P.append(('JMP', 'P1'))
    lab['P2INIT'] = len(P)
    P.append(('SETI', 'I', 0))
    lab['P2'] = len(P)
    P.append(('JGE', 'I', 'M', 'ACCEPT'))
    P.append(('LOAD', 'V', 'I'))
    P.append(('JZ', 'V', 'REJECT'))
    P.append(('JGT', 'V', 'M', 'REJECT'))
    P.append(('SUBI', 'T', 'V', 1))
    P.append(('INP', 'U', 'T'))                    # U <- f(V-1)
    P.append(('JNE', 'U', 'I', 'REJECT'))
    P.append(('ADDI', 'I', 'I', 1))
    P.append(('JMP', 'P2'))
    lab['ACCEPT'] = len(P); P.append(('HALT', 'accept'))
    lab['REJECT'] = len(P); P.append(('HALT', 'reject'))
    lab['FALLBACK'] = len(P); P.append(('HALT', 'fallback'))
    prog = []
    for ins in P:
        prog.append(tuple(lab[a] if isinstance(a, str) and a in lab and a not in REGS else a
                          for a in ins))
    return prog, lab


def width(m, prog):
    return max((m + 1).bit_length(), len(prog).bit_length(), 2)


def step(prog, read, write, F, m, mask):
    pc = read(PC)
    if pc >= len(prog):
        return                                     # outside the text: idle
    ins = prog[pc]
    op = ins[0]
    nxt = pc + 1
    if op == 'HALT':
        return                                     # halted states idle
    if op == 'LEN':
        write(R[ins[1]], m & mask)
    elif op == 'SHR':
        write(R[ins[1]], read(R[ins[2]]) >> 1)
    elif op == 'SETI':
        write(R[ins[1]], ins[2] & mask)
    elif op == 'ADDI':
        write(R[ins[1]], (read(R[ins[2]]) + ins[3]) & mask)
    elif op == 'SUBI':
        write(R[ins[1]], (read(R[ins[2]]) - ins[3]) & mask)
    elif op == 'LT':
        write(R[ins[1]], 1 if read(R[ins[2]]) < read(R[ins[3]]) else 0)
    elif op == 'INP':
        idx = read(R[ins[2]])
        write(R[ins[1]], (F[idx] if idx < len(F) else 0) & mask)
    elif op == 'LOAD':
        write(R[ins[1]], read(('m', read(R[ins[2]]))))
    elif op == 'STORE':
        a = read(R[ins[1]]); v = read(R[ins[2]])
        write(('m', a), v)
    elif op == 'JGE':
        if read(R[ins[1]]) >= read(R[ins[2]]): nxt = ins[3]
    elif op == 'JGT':
        if read(R[ins[1]]) > read(R[ins[2]]): nxt = ins[3]
    elif op == 'JEQ':
        if read(R[ins[1]]) == read(R[ins[2]]): nxt = ins[3]
    elif op == 'JNE':
        if read(R[ins[1]]) != read(R[ins[2]]): nxt = ins[3]
    elif op == 'JZ':
        if read(R[ins[1]]) == 0: nxt = ins[2]
    elif op == 'JMP':
        nxt = ins[1]
    else:
        raise ValueError(op)
    write(PC, nxt)


class TrueState:
    def __init__(self):
        self.w = {}
    def read(self, x):
        return self.w.get(x, 0)
    def write(self, x, v):
        if v == 0:
            self.w.pop(x, None)
        else:
            self.w[x] = v


def schedule(m, g, family):
    """Cut times (computable from m, g and the fixed program): list of (kind, G, time)."""
    c1 = 8 if family == 'main' else 6              # instructions per phase-1 iteration
    c2 = 9                                         # per phase-2 iteration
    cuts = [('init', None, 0)]
    G = 0
    while G < 2 * m:
        if G < m:
            cuts.append(('p1', G, 3 + c1 * G))
        else:
            cuts.append(('p2', G - m, 3 + c1 * m + 2 + c2 * (G - m)))
        G += g
    cuts.append(('halt', None, 3 + c1 * m + 2 + c2 * m + 1))
    return cuts

# ---------------------------------------------------------------- bank

def landmark_pairs(f, h):
    """Cycle-landmark directory: marks every h along each cycle of length > h."""
    m = len(f)
    seen = [False] * m
    pairs = {}
    for s in range(m):
        if seen[s]:
            continue
        cyc = []
        x = s
        while not seen[x]:
            seen[x] = True
            cyc.append(x)
            x = f[x]
        if len(cyc) > h:
            marks = cyc[::h]
            for i, mk in enumerate(marks):
                pairs[mk] = marks[i - 1]
    return pairs


def encode_bank(m, g, h, pairs):
    wb = max(1, (max(m, g, h, len(pairs)) ).bit_length())
    assert wb < 64
    out = [format(wb, '06b'), format(g, f'0{wb}b'), format(h, f'0{wb}b'),
           format(len(pairs), f'0{wb}b')]
    for mk in sorted(pairs):
        out.append(format(mk, f'0{wb}b'))
        out.append(format(pairs[mk], f'0{wb}b'))
    return ''.join(out)

# ---------------------------------------------------------------- evaluator

class Evaluator:
    """Sees only: the file bytes, the bank bits, the family (part of its fixed text)."""

    def __init__(self, data, bank, family, hcap):
        self.data = data
        self.bank = bank
        self.family = family
        self.hcap = hcap          # format parameter, fixed before f is chosen (bounds E)
        self.cache = {}
        self.decode_probes_max = 0
        self.probes = 0
        self.c = 0

    # counted primitives -------------------------------------------------
    def _byte(self, pos):
        self.c += 1
        return self.data[pos] if 0 <= pos < len(self.data) else 0x20

    def _field(self, pos, wdt):
        self.c += 1
        s = self.bank[pos:pos + wdt]
        return int(s, 2) if len(s) == wdt and wdt > 0 else 0

    def _header(self):
        pos = 0
        txt = []
        while True:
            b = self._byte(pos)
            if b == 10 or pos > 64:
                break
            txt.append(chr(b)); pos += 1
        parts = ''.join(txt).split()
        V, C = int(parts[2]), int(parts[3])
        self.hlen = pos + 1
        self.D = len(str(V))
        self.rowlen = 3 * self.D + 8
        if self.family == 'main':
            self.m = V - 3; self.r0 = 7 + self.m
        else:
            self.m = (V - 3) // 2; self.r0 = 3 * self.m + 7

    def _f(self, x):
        """One probe: parse the first literal of unit row x; returns |lit| - 4."""
        self.probes += 1
        if not (0 <= x < self.m):
            return 0
        base = self.hlen + (self.r0 + x) * self.rowlen
        val = 0
        for p in range(base, base + self.D + 1):
            b = self._byte(p)
            if 48 <= b <= 57:
                val = 10 * val + (b - 48)
        return val - 4

    def _bankhdr(self):
        self.wb = self._field(0, 6)
        wb = self.wb
        self.g = self._field(6, wb)
        self.h = self._field(6 + wb, wb)
        self.K = self._field(6 + 2 * wb, wb)
        self.dir0 = 6 + 3 * wb

    def _pred_mark(self, x):
        lo, hi = 0, self.K
        wb = self.wb
        while lo < hi:
            mid = (lo + hi) // 2
            key = self._field(self.dir0 + 2 * wb * mid, wb)
            if key == x:
                return self._field(self.dir0 + 2 * wb * mid + wb, wb)
            if key < x:
                lo = mid + 1
            else:
                hi = mid
        return None

    def _decode(self, y):
        """Cycle-landmark inversion; capped at 2*min(h, hcap)+2 forward probes, where h is
        the bank's field and hcap the format's parameter; returns f^{-1}(y)."""
        self.probes = 0
        cap = 2 * min(self.h, self.hcap) + 2
        x = y
        while True:
            pm = self._pred_mark(x)
            if pm is not None:
                break
            if self.probes >= cap:
                return 0
            z = self._f(x)
            if z == y:
                self.decode_probes_max = max(self.decode_probes_max, self.probes)
                return x
            x = z
        x = pm
        while self.probes < cap:
            z = self._f(x)
            if z == y:
                self.decode_probes_max = max(self.decode_probes_max, self.probes)
                return x
            x = z
        return 0

    # the row map ----------------------------------------------------------
    def word(self, k, x):
        """(value, cost) of word x in row k.  A bit query costs the same as the word."""
        key = (k, x)
        if key in self.cache:
            return self.cache[key]
        self.c = 0
        self._header()
        self._bankhdr()
        m, g = self.m, self.g
        n1 = -(-2 * m // g) if g > 0 else 0
        if k == 0:
            kind, G = 'init', None
        elif 1 <= k <= n1:
            G = (k - 1) * g
            kind = 'p1' if G < m else 'p2'
        elif k == n1 + 1:
            kind, G = 'halt', None
        else:
            kind, G = 'none', None
        prog, lab = PROGS[self.family]
        val = 0
        if kind == 'init' or kind == 'none':
            val = 0
        elif x == PC:
            val = {'p1': lab['P1'], 'p2': lab['P2'], 'halt': lab['ACCEPT']}[kind]
        elif x[0] == 'r':
            r = x[1]
            if r == 'M':
                val = m
            elif r == 'H':
                val = m >> 1
            elif kind == 'p1':
                i = G
                val = {'I': i, 'A': self._f(i - 1) if i >= 1 else 0, 'V': 0,
                       'T': i, 'U': 0}[r]
            else:
                y = G - m if kind == 'p2' else m
                if r == 'I':
                    val = y
                elif r == 'A':
                    val = self._f(m - 1) if m >= 1 else 0
                elif y == 0:
                    val = {'V': 0, 'T': m, 'U': 0}[r]
                else:
                    if r == 'U':
                        val = y - 1
                    else:
                        j = self._decode(y - 1)
                        val = j + 1 if r == 'V' else j
        else:
            a = x[1]
            if 0 <= a < m:
                j = self._decode(a)
                if kind == 'p1':
                    val = j + 1 if j < G else 0
                else:
                    val = j + 1
            else:
                val = 0
        val &= MASK[0]
        res = (val, self.c + 1)
        self.cache[key] = res
        return res


PROGS = {fam: program(fam) for fam in ('main', 'first')}
MASK = [0]

# ---------------------------------------------------------------- checking one chart

def true_snapshots(f, family, cuts, W):
    prog, lab = PROGS[family]
    m = len(f)
    mask = (1 << W) - 1
    st = TrueState()
    snaps = []
    t = 0
    for (kind, G, tau) in cuts:
        while t < tau:
            step(prog, st.read, st.write, f, m, mask)
            t += 1
        snaps.append(dict(st.w))
    return snaps


def check_chart(f, family, data, bank, hcap, W, guard, want_cost=False, snaps=None):
    """Return (checker_accepts, rows_all_true, stats)."""
    prog, lab = PROGS[family]
    m = len(f)
    mask = (1 << W) - 1
    MASK[0] = mask
    ev = Evaluator(data, bank, family, hcap)
    # The checker computes the schedule from the bank's g (a malformed g gives some schedule).
    ev.c = 0; ev._header(); ev._bankhdr()
    g = ev.g if ev.g > 0 else 1
    cuts = schedule(m, g, family)
    if snaps is None:
        snaps = true_snapshots(f, family, cuts, W)
    base = [PC] + [R[r] for r in REGS] + [('m', a) for a in range(m)] + [('m', a) for a in guard]
    ok = True
    # initial condition: row 0 vs genuine initial configuration (all zero)
    for x in base:
        if ev.word(0, x)[0] != 0:
            ok = False
    stats = {'q_max': 0, 'R_max': 0, 'E_max': 0, 'gaps': len(cuts) - 1}
    touched_all = set()
    for k in range(len(cuts) - 1):
        overlay = {}
        entry = {}
        cost = [0]
        def read(x):
            if x in overlay:
                return overlay[x]
            if x not in entry:
                v, c = ev.word(k, x)
                entry[x] = v
                cost[0] += W * c                   # W bit calls, each costing c
            return entry[x]
        def write(x, v):
            overlay[x] = v
        steps = cuts[k + 1][2] - cuts[k][2]
        for _ in range(steps):
            step(prog, read, write, f, m, mask)
        q = W * len(entry)
        uni = set(base) | set(overlay) | set(entry)
        touched_all |= set(overlay) | set(entry)
        worst = 0
        for x in uni:
            if x in overlay:
                e, ce = overlay[x], 0
            elif x in entry:
                e, ce = entry[x], 0
            else:
                e, ce = ev.word(k, x)
            n, cn = ev.word(k + 1, x)
            if e != n:
                ok = False
            worst = max(worst, ce + cn)
        Rk = steps + cost[0] + worst
        stats['q_max'] = max(stats['q_max'], q)
        stats['R_max'] = max(stats['R_max'], Rk)
    # terminal condition
    last = len(cuts) - 1
    if ev.word(last, PC)[0] != lab['ACCEPT']:
        ok = False
    # cross-check every row against the direct simulation
    rows_true = True
    for k in range(len(cuts)):
        uni = set(base) | touched_all | {x for x in snaps[k]}
        for x in uni:
            if ev.word(k, x)[0] != snaps[k].get(x, 0):
                rows_true = False
                break
        if not rows_true:
            break
    stats['E_max'] = max(c for (_, c) in ev.cache.values())
    stats['probes_max'] = ev.decode_probes_max
    stats['bank_bits'] = len(bank)
    stats['rows'] = len(cuts)
    # the genuine run must actually be at the claimed loop heads and accept
    for (kind, G, tau), sn in zip(cuts, snaps):
        pcv = sn.get(PC, 0)
        exp = {'init': 0, 'p1': lab['P1'], 'p2': lab['P2'], 'halt': lab['ACCEPT']}[kind]
        assert pcv == exp, (kind, G, tau, pcv, exp)
    return ok, rows_true, stats


def make_file(f, family):
    return pinned_file(f) if family == 'main' else missing_file(f)


def cbrt_ceil(m):
    h = 1
    while h ** 3 < m:
        h += 1
    return h

# ---------------------------------------------------------------- drivers

def bank_for(f, g, h):
    return encode_bank(len(f), g, h, landmark_pairs(f, h))


def mode_exhaustive():
    from collections import Counter
    tally = Counter()
    worst = {}
    for m in (2, 4, 6):
        for fam in ('main', 'first'):
            prog, _ = PROGS[fam]
            W = width(m, prog)
            for f in permutations(range(m)):
                data = make_file(list(f), fam)
                for h in range(1, m + 1):
                    for g in range(1, m + 1):
                        bank = bank_for(f, g, h)
                        ok, rt, st = check_chart(list(f), fam, data, bank, h, W,
                                                 guard=[m, m + 1, (1 << W) - 1])
                        assert ok and rt, (m, fam, f, h, g)
                        assert st['probes_max'] <= max(1, 2 * h - 1), (m, f, h, st)
                        tally[(m, fam)] += 1
                        key = (m, fam, h, g)
                        w0 = worst.get(key, (0, 0, 0, 0))
                        worst[key] = tuple(max(a, b) for a, b in zip(
                            w0, (st['bank_bits'], st['probes_max'], st['q_max'], st['R_max'])))
    print("all (h,g) in [1..m]^2, every permutation, both families: charts sound:",
          dict(sorted(tally.items())))
    for key in [(6, 'main', 2, 2), (6, 'first', 2, 2), (6, 'main', 1, 1), (6, 'main', 6, 6)]:
        print("  max over perms (bank bits, decode probes, q, R) at (m,fam,h,g) =", key, worst[key])
    # m = 8, h = g = ceil(8^(1/3)) = 2
    for fam in ('main', 'first'):
        m = 8
        prog, _ = PROGS[fam]
        W = width(m, prog)
        h = g = cbrt_ceil(m)
        mx = (0, 0, 0, 0)
        n = 0
        for f in permutations(range(m)):
            data = make_file(list(f), fam)
            bank = bank_for(f, g, h)
            ok, rt, st = check_chart(list(f), fam, data, bank, h, W, guard=[m, m + 1, (1 << W) - 1])
            assert ok and rt, (fam, f)
            mx = tuple(max(a, b) for a, b in zip(mx, (st['bank_bits'], st['probes_max'],
                                                      st['q_max'], st['R_max'])))
            n += 1
        print(f"m=8 family={fam} h=g={h} W={W}: {n} permutations, all charts sound; "
              f"max (bank bits, decode probes, q, R) = {mx}, rows = {st['rows']}")
    # decoder alone, m = 8, all h
    n = 0
    for f in permutations(range(8)):
        for h in range(1, 9):
            pairs = landmark_pairs(f, h)
            assert h * len(pairs) < 2 * 8 or (len(pairs) == 0)
            data = pinned_file(list(f))
            ev = Evaluator(data, encode_bank(8, 1, h, pairs), 'main', h)
            ev.c = 0; ev._header(); ev._bankhdr()
            for a in range(8):
                ev.c = 0
                j = ev._decode(a)
                assert f[j] == a and ev.probes <= max(1, 2 * h - 1), (f, h, a, ev.probes)
                n += 1
    print(f"decoder alone, m=8, h=1..8: {n} inversions correct, probes <= 2h-1, K*h < 2m")


def corrupt(bank, rng, kind, f, g, h):
    m = len(f)
    if kind == 'flip':
        i = rng.randrange(len(bank))
        return bank[:i] + ('1' if bank[i] == '0' else '0') + bank[i + 1:]
    pairs = landmark_pairs(f, h)
    if not pairs:
        return None
    keys = sorted(pairs)
    if kind == 'pred':
        k = rng.choice(keys)
        other = rng.choice([x for x in range(m) if x != pairs[k]])
        pairs[k] = other
    elif kind == 'drop':
        del pairs[rng.choice(keys)]
    elif kind == 'add':
        cand = [x for x in range(m) if x not in pairs]
        if not cand:
            return None
        pairs[rng.choice(cand)] = rng.randrange(m)
    return encode_bank(m, g, h, pairs)


def mode_mutation():
    from collections import Counter
    rng = random.Random(20261127)
    tally = Counter()
    for m in (4, 6):
        for fam in ('main', 'first'):
            prog, _ = PROGS[fam]
            W = width(m, prog)
            for f in permutations(range(m)):
                data = make_file(list(f), fam)
                for (h, g) in ((1, 1), (2, 2), (2, 1), (3, 2)):
                    good = bank_for(f, g, h)
                    for kind in ('flip', 'flip', 'flip', 'pred', 'drop', 'add'):
                        bad = corrupt(good, rng, kind, list(f), g, h)
                        if bad is None or bad == good:
                            continue
                        # hcap = the honest h: the format's parameter, fixed before f.
                        ok, rt, st = check_chart(list(f), fam, data, bad, h, W,
                                                 guard=[m, m + 1, (1 << W) - 1])
                        assert ok == rt, (m, fam, f, h, g, kind)
                        tally[(kind, 'accepted' if ok else 'rejected')] += 1
    print("corrupted banks: checker verdict == (all rows equal the true snapshots) in every case:",
          dict(sorted(tally.items(), key=str)))


def mode_scale(ms, seed=1, rule='cbrt'):
    rng = random.Random(seed)
    print('rule:', rule, '(cbrt: h = g = ceil(m^(1/3)); sqrt1: g = 1, h = ceil(m^(1/2)))')
    print(" m      N(bits)  h=g  W  K(marks) bank_bits  m^(2/3)log2m  probes_max  E_max  q_max  R_max  rows  gaps_sampled")
    for m in ms:
        fam = 'main'
        f = list(range(m)); rng.shuffle(f)
        prog, _ = PROGS[fam]
        W = width(m, prog)
        if rule == 'cbrt':
            h = g = cbrt_ceil(m)
        else:
            g = 1; h = math.isqrt(m - 1) + 1
        pairs = landmark_pairs(f, h)
        bank = encode_bank(m, g, h, pairs)
        data = make_file(f, fam)
        sample = sorted(rng.sample(range(m), min(m, 48)))
        MASK[0] = (1 << W) - 1
        ok, rt, st = check_chart_sampled(f, fam, data, bank, W, sample, h)
        assert ok and rt
        print(f"{m:6d} {8*len(data):10d} {h:3d} {W:2d} {len(pairs):8d} {len(bank):9d} "
              f"{m**(2/3)*math.log2(m):12.0f} {st['probes_max']:10d} {st['E_max']:6d} "
              f"{st['q_max']:6d} {st['R_max']:7d} {st['rows']:5d} {st['gaps']:5d}")


def check_chart_sampled(f, family, data, bank, W, sample, hcap):
    """As check_chart, with memory coordinates restricted to `sample` plus touched words."""
    prog, lab = PROGS[family]
    m = len(f)
    mask = (1 << W) - 1
    MASK[0] = mask
    ev = Evaluator(data, bank, family, hcap)
    ev.c = 0; ev._header(); ev._bankhdr()
    g = ev.g
    cuts = schedule(m, g, family)
    base = [PC] + [R[r] for r in REGS] + [('m', a) for a in sample] + [('m', m), ('m', mask)]
    keep = set(base)
    # true snapshots restricted to base
    st_ = TrueState(); t = 0; snaps = []
    for (kind, G, tau) in cuts:
        while t < tau:
            step(prog, st_.read, st_.write, f, m, mask); t += 1
        snaps.append({x: st_.w[x] for x in keep if x in st_.w})
        exp = {'init': 0, 'p1': lab['P1'], 'p2': lab['P2'], 'halt': lab['ACCEPT']}[kind]
        assert st_.read(PC) == exp
    ok = all(ev.word(0, x)[0] == 0 for x in base)
    stats = {'q_max': 0, 'R_max': 0, 'gaps': len(cuts) - 1}
    for k in range(len(cuts) - 1):
        overlay, entry, cost = {}, {}, [0]
        def read(x):
            if x in overlay: return overlay[x]
            if x not in entry:
                v, c = ev.word(k, x); entry[x] = v; cost[0] += W * c
            return entry[x]
        def write(x, v): overlay[x] = v
        steps = cuts[k + 1][2] - cuts[k][2]
        for _ in range(steps):
            step(prog, read, write, f, m, mask)
        worst = 0
        for x in set(base) | set(overlay) | set(entry):
            if x in overlay: e, ce = overlay[x], 0
            elif x in entry: e, ce = entry[x], 0
            else: e, ce = ev.word(k, x)
            n, cn = ev.word(k + 1, x)
            ok &= (e == n)
            worst = max(worst, ce + cn)
        stats['q_max'] = max(stats['q_max'], W * len(entry))
        stats['R_max'] = max(stats['R_max'], steps + cost[0] + worst)
        # free memory of row k-1
        for key in [key for key in ev.cache if key[0] == k - 1]:
            del ev.cache[key]
    ok &= ev.word(len(cuts) - 1, PC)[0] == lab['ACCEPT']
    rt = all(ev.word(k, x)[0] == snaps[k].get(x, 0) for k in range(len(cuts)) for x in base)
    stats['E_max'] = max(c for (_, c) in ev.cache.values())
    stats['probes_max'] = ev.decode_probes_max
    stats['rows'] = len(cuts)
    return ok, rt, stats


def mode_smoke():
    """Default without arguments: the exhaustive check of mode_exhaustive at m = 2 and 4 only."""
    from collections import Counter
    tally = Counter()
    for m in (2, 4):
        for fam in ('main', 'first'):
            prog, _ = PROGS[fam]
            W = width(m, prog)
            for f in permutations(range(m)):
                data = make_file(list(f), fam)
                for h in range(1, m + 1):
                    for g in range(1, m + 1):
                        ok, rt, st = check_chart(list(f), fam, data, bank_for(f, g, h), h, W,
                                                 guard=[m, m + 1, (1 << W) - 1])
                        assert ok and rt, (m, fam, f, h, g)
                        assert st['probes_max'] <= max(1, 2 * h - 1), (m, f, h, st)
                        tally[(m, fam)] += 1
    print("smoke test, m = 2 and 4 (modes exhaustive, mutation, scale, scale1 run the full checks):")
    print("all (h,g) in [1..m]^2, every permutation, both families: charts sound:",
          dict(sorted(tally.items())))


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'smoke'
    if what == 'smoke':
        mode_smoke()
    elif what == 'exhaustive':
        mode_exhaustive()
    elif what == 'mutation':
        mode_mutation()
    elif what == 'scale':
        mode_scale([int(a) for a in sys.argv[2:]])
    elif what == 'scale1':
        mode_scale([int(a) for a in sys.argv[2:]], rule='sqrt1')
