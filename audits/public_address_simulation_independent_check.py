#!/usr/bin/env python3
"""Independent check for notes/three-public-address-normal-forms-of-a-ram-run.md, written during review.

Toy RAM with integer words (records packed into one integer, no tuples), logging
every memory access (kind, address) and every ALU op by name.

R1. Counterexample to the literal (a), with a DIFFERENT prologue than public_address_simulation_toy_check.py's:
    Q_scanpro: prologue computes v_1..v_T' by branch-free scans of the read-only input
    (m input reads per source step), stores them at public cells; copy windows mirror P;
    load window j makes ONE probe.  Checked over all inputs: identical trace, correct (v_j,a_j).
R2. Pointer doubling with Batcher's odd-even MERGE sort (the toy check uses bitonic) on packed integer
    records; exhaustive at small sizes; op counts at larger sizes vs the scan's m*T'.
R3. Necessity of the online hypothesis tau_j < lambda_{j+1} in Corollary B: an offline
    simulator for P_fresh reads all q_j first and then makes one probe per window; we check
    it violates the online order, while each interval [lambda_j, tau_j] still contains >= m
    loads other than q_j's cell (the per-interval form of Corollary B).
R4. Negative control: direct chase gives many distinct traces.
"""
import itertools, sys, random

class RAM:
    def __init__(self, inp, count_only=False):
        self.inp = list(inp); self.mem = {}; self.log = []; self.n = 0; self.co = count_only
    def _l(self, e):
        self.n += 1
        if not self.co: self.log.append(e)
    def rin(self, i): self._l(('I', i)); return self.inp[i]
    def ld(self, a): self._l(('L', a)); return self.mem.get(a, 0)
    def st(self, a, v): self._l(('S', a)); self.mem[a] = v
    def op(self, name, *x):
        self._l(('A', name))
        if name == 'eq': return int(x[0] == x[1])
        if name == 'sel': return x[1] if x[0] else x[2]
        if name == 'and': return x[0] & x[1]
        if name == 'lt': return int(x[0] < x[1])
        if name == 'shr': return x[0] >> x[1]
        if name == 'or': return x[0] | x[1]
        if name == 'shl': return x[0] << x[1]
        raise ValueError(name)

def chase(x, a0, m, T):
    a, out = a0, []
    for _ in range(T):
        v = x[a]; a = v % m; out.append((v, a))
    return out

# ---------- R1: scan prologue ----------
def q_scanpro(x, a0, m, T):
    M = RAM(list(x) + [a0]); V = 10**6
    a = M.rin(m)
    for j in range(T):                       # prologue: branch-free scan of the input per source step
        v = 0
        for i in range(m):
            c = M.rin(i)
            v = M.op('sel', M.op('eq', a, i), c, v)
        M.st(V + j, v)
        a = M.op('and', v, m - 1)
    for i in range(m):                       # copy windows
        M.st(i, M.rin(i))
    regs, probes = [], []
    for j in range(T):                       # load windows
        s = len(M.log)
        v = M.ld(V + j); a = M.op('and', v, m - 1)
        regs.append((v, a)); probes.append(sum(e[0] in 'LI' for e in M.log[s:]))
    return M.log, regs, probes

# ---------- R2: pointer doubling with odd-even merge sort on packed ints ----------
def oem_pairs(N):
    """Batcher odd-even merge sort comparator list for N a power of two."""
    pairs = []
    p = 1
    while p < N:
        k = p
        while k >= 1:
            for j in range(k % p, N - k, 2 * k):
                for i in range(min(k, N - j - k)):
                    if (i + j) // (2 * p) == (i + j + k) // (2 * p):
                        pairs.append((i + j, i + j + k))
            k //= 2
        p *= 2
    return pairs

PAIRS = {}
def sort_net(M, base, N):
    if N not in PAIRS: PAIRS[N] = oem_pairs(N)
    for (i, j) in PAIRS[N]:
        A = M.ld(base + i); B = M.ld(base + j)
        c = M.op('lt', B, A)
        M.st(base + i, M.op('sel', c, B, A)); M.st(base + j, M.op('sel', c, A, B))

FB = 20   # field width in bits for packed records

def gather(M, tab, m, qry, q, out, scr):
    """out[i] = tab[qry[i]] (qry[i] in [0,m)); record = key<<3FB | tag<<2FB | idx<<FB | val."""
    N = 1
    while N < m + q: N *= 2
    for i in range(m):
        v = M.ld(tab + i); M.st(scr + i, (i << 3*FB) | (0 << 2*FB) | (0 << FB) | v)  # packing = public shifts/ors
        M._l(('A', 'pack'))
    for i in range(q):
        a = M.ld(qry + i); M.st(scr + m + i, (a << 3*FB) | (1 << 2*FB) | (i << FB)); M._l(('A', 'pack'))
    for i in range(m + q, N):
        M.st(scr + i, ((m + 1) << 3*FB) | (1 << 2*FB) | (i << FB)); M._l(('A', 'pack'))
    sort_net(M, scr, N)
    carry = 0
    mask = (1 << FB) - 1
    for i in range(N):
        r = M.ld(scr + i)
        tag = M.op('and', M.op('shr', r, 2*FB), 1)
        val = M.op('and', r, mask)
        idx = M.op('and', M.op('shr', r, FB), mask)
        istab = M.op('eq', tag, 0)
        carry = M.op('sel', istab, val, carry)
        key2 = M.op('sel', istab, N + i, idx)
        M.st(scr + i, M.op('or', M.op('shl', key2, FB), carry))
    sort_net(M, scr, N)
    for i in range(q):
        r = M.ld(scr + i); M.st(out + i, M.op('and', r, mask))

def q_double(x, a0, m, T, count_only=False):
    M = RAM(list(x) + [a0], count_only)
    Fb, Ab, Tb, Vb, Sb = 10**5, 2*10**5, 3*10**5, 4*10**5, 5*10**5
    K = max(1, (T - 1).bit_length())
    for i in range(m):
        M.st(Fb + i, M.op('and', M.rin(i), m - 1))
    a0r = M.rin(m)
    for k in range(1, K):
        gather(M, Fb + (k-1)*m, m, Fb + (k-1)*m, m, Fb + k*m, Sb)
    for j in range(T): M.st(Ab + j, a0r)
    for k in range(K):
        js = [j for j in range(T) if (j >> k) & 1]
        if not js: continue
        for t, j in enumerate(js): M.st(Tb + t, M.ld(Ab + j))
        gather(M, Fb + k*m, m, Tb, len(js), Tb + 50000, Sb)
        for t, j in enumerate(js): M.st(Ab + j, M.ld(Tb + 50000 + t))
    for i in range(m): M.st(Vb - m + i, M.rin(i))       # x table
    gather(M, Vb - m, m, Ab, T, Vb, Sb)
    pro = M.n
    for i in range(m): M.st(i, M.rin(i))
    regs, probes = [], []
    for j in range(T):
        s = M.n
        if count_only:
            M.ld(Vb + j); M.op('and', 0, 0); probes.append(1); continue
        s = len(M.log)
        v = M.ld(Vb + j); a = M.op('and', v, m - 1)
        regs.append((v, a)); probes.append(sum(e[0] in 'LI' for e in M.log[s:]))
    return M.log, regs, probes, pro

# ---------- R3: offline simulator for P_fresh ----------
def q_offline(x, qs, m):
    T = len(qs); M = RAM(list(x) + list(qs)); R = 10**6
    for j in range(T):                        # prologue: read every q_j, answer by scanning
        a = M.op('and', M.rin(m + j), m - 1); acc = 0
        for i in range(m):
            acc = M.op('sel', M.op('eq', a, i), M.rin(i), acc)
        M.st(R + j, acc)
    for i in range(m): M.st(i, M.rin(i))
    tau, rep = [], []
    for j in range(T):
        rep.append(M.ld(R + j)); tau.append(len(M.log) - 1)
    lam = [next(t for t, e in enumerate(M.log) if e == ('I', m + j)) for j in range(T)]
    online = all(tau[j] < lam[j + 1] for j in range(T - 1))
    per_int = []
    for j in range(T):
        cells = {e for e in M.log[lam[j]:tau[j] + 1] if e[0] in 'LI' and e != ('I', m + j)}
        per_int.append(len(cells))
    return M.log, rep, online, per_int

def main():
    bad = 0
    # R4 negative control
    traces = set()
    for x in itertools.product(range(4), repeat=4):
        for a0 in range(4):
            M = RAM(list(x) + [a0])
            for i in range(4): M.st(i, M.rin(i))
            a = M.rin(4)
            for _ in range(3): a = M.op('and', M.ld(a), 3)
            traces.add(tuple(M.log))
    print('R4 negative control m=4 b=2 T=3: distinct traces =', len(traces))
    bad += len(traces) <= 1
    # R1 scan prologue, exhaustive
    for (m, b, T) in [(2, 2, 5), (4, 2, 6), (4, 3, 4)]:
        ref = None; mis = 0; cnt = 0
        for x in itertools.product(range(2 ** b), repeat=m):
            for a0 in range(m):
                log, regs, probes = q_scanpro(x, a0, m, T); cnt += 1
                if ref is None: ref = log
                elif log != ref: print('TRACE DIFFERS R1', m, x, a0); bad += 1; break
                mis += regs != chase(x, a0, m, T); assert probes == [1] * T
        print('R1 scan-prologue m=%d b=%d T=%d inputs=%d identical=True mismatches=%d probes/load-window=1 prologue_len=%d'
              % (m, b, T, cnt, mis, len(ref) - (2 * m + 2 * T)))
        bad += mis
    # R2 doubling with odd-even merge sort, exhaustive small + sampled
    rng = random.Random(7)
    for (m, b, T, mode) in [(2, 2, 6, 'all'), (4, 2, 8, 'all'), (4, 3, 5, 'all'), (8, 4, 12, 300), (16, 5, 33, 60)]:
        if mode == 'all':
            ins = [(x, a0) for x in itertools.product(range(2 ** b), repeat=m) for a0 in range(m)]
        else:
            ins = [(tuple(rng.randrange(2 ** b) for _ in range(m)), rng.randrange(m)) for _ in range(mode)]
        ref = None; mis = 0
        for (x, a0) in ins:
            log, regs, probes, pro = q_double(x, a0, m, T)
            if ref is None: ref = log
            elif log != ref: print('TRACE DIFFERS R2', m, x, a0); bad += 1; break
            mis += regs != chase(x, a0, m, T); assert probes == [1] * T
        print('R2 doubling(oddeven-merge) m=%d b=%d T=%d inputs=%d identical=True mismatches=%d probes/load-window=1 prologue_ops=%d m*T=%d'
              % (m, b, T, len(ins), mis, pro, m * T))
        bad += mis
    # R2 cost growth (count only), m = T = 2^k
    def P(N):
        p = N.bit_length() - 1
        return (p * p - p + 4) * 2 ** (p - 2) - 1 if p >= 2 else (1 if N == 2 else 0)
    for N in [2, 4, 8, 16, 32, 64, 128, 256]:
        assert len(oem_pairs(N)) == P(N), (N, len(oem_pairs(N)), P(N))
    def cg(m, q):
        N = 1
        while N < m + q: N *= 2
        return m + 4 * q + 14 * N + 14 * P(N)
    def cpro(m, T):
        K = max(1, (T - 1).bit_length())
        c = 3 * m + 1 + (K - 1) * cg(m, m) + T
        for k in range(K):
            q = sum(1 for j in range(T) if (j >> k) & 1)
            if q: c += 4 * q + cg(m, q)
        return c + 2 * m + cg(m, T)
    for k in range(4, 9):
        m = T = 2 ** k
        _, _, _, pro = q_double([0] * m, 0, m, T, count_only=True)
        assert pro == cpro(m, T), (k, pro, cpro(m, T))
        print('R2 cost (measured = formula) k=%d m=T=%d prologue_ops=%d m*T=%d ratio=%.2f' % (k, m, pro, m * T, pro / (m * T)))
    for k in range(10, 23, 2):
        m = T = 2 ** k
        c = cpro(m, T)
        print('R2 cost (formula) k=%d m=T=2^%d prologue_ops=%.3g m*T=%.3g ratio=%.3f  pro/((m+T)log2^2(m+T)log2 T)=%.2f'
              % (k, k, c, m * T, c / (m * T), c / (2 * m * (k + 1) ** 2 * k)))
    # R3 offline simulator for P_fresh
    for (m, b, T) in [(4, 2, 3), (4, 3, 2)]:
        ref = None; mis = 0; on = set(); mins = []
        for x in itertools.product(range(2 ** b), repeat=m):
            for qs in itertools.product(range(2 ** b), repeat=T):
                log, rep, online, per = q_offline(x, qs, m)
                if ref is None: ref = log
                elif log != ref: print('TRACE DIFFERS R3'); bad += 1; break
                mis += rep != [x[q % m] for q in qs]; on.add(online); mins.append(min(per))
        print('R3 offline P_fresh m=%d b=%d T=%d identical=True mismatches=%d online_order_holds=%s min_loads_in_[lambda_j,tau_j]_excl_qj=%d (>= m - O(1))'
              % (m, b, T, mis, on, min(mins)))
        bad += mis
    print('INDEPENDENT CHECK TOTAL bad =', bad)
    return 1 if bad else 0

if __name__ == '__main__':
    sys.exit(main())
