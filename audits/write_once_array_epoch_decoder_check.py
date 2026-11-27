#!/usr/bin/env python3
"""Sampled check of the epoch-encoding argument of Lemma A of
notes/mutable-arrays-on-word-write-once-memory.md.

Model W: write-once cells, O(1) mutable registers, no load of an unwritten cell.
Two array schemes are simulated on uniformly random update sequences
(n = m updates, index uniform in [m], value uniform in [1, 2^w)), followed by
a read at every q in [m]:

  * PC(F): path copying in an F-ary trie (Irani-Naor-Rubinfeld Thm 3.1 shape).
           Lies in model W.
  * VA:    versioned addresses, cell (i, k) = k-th version of index i, found by
           galloping + binary search over unwritten cells (INR Thm 3.2 shape).
           Loads unwritten cells, so it is NOT in model W.

For each epoch j (epoch j = the B^j updates ending Lambda_{j-1} updates
before the read, Lambda_j = B + ... + B^j) the decoder of the proof is run:
it knows every cell written before epoch j, receives the final registers and
the cells written after epoch j, simulates the reader for every q, aborts at
the first load of an address it does not know, and reconstructs the index
set I_j of epoch j from the reader outputs plus the correction list (the part
of I_j \\ P_j inside the aborted set, I_j cap P_j, and value coincidences).

Checked, per run and epoch:
  (1) decoder output == true I_j                       (decoding is correct)
  (2) in model W, every aborted load hits a cell written in epoch j
  (3) in model W, sum_j beta_j <= mean read probes, beta_j = |Bad_j| / m
  (4) message length vs log2 C(m, |I_j|) (reported, not asserted)
For VA, (2) and (3) fail by design: an abort may be a load of an unwritten
cell, and one such load makes q "bad" for every epoch at once.

Usage: python3 write_once_array_epoch_decoder_check.py [m_log2=12] [seeds=3]   (about 2 s)
"""
import math
import random
import sys

W_BITS = 32           # nominal word width used only for message-length accounting
UNWRITTEN = None


class Memory:
    """Write-once memory. Cells are (time, content). Fresh addresses come from a
    bump allocator unless an explicit address is given (VA scheme)."""

    def __init__(self, allow_unwritten_loads):
        self.cells = {}
        self.next = 0
        self.allow_unwritten = allow_unwritten_loads

    def write(self, t, content, addr=None):
        if addr is None:
            addr = self.next
            self.next += 1
        assert addr not in self.cells, "write-once violated"
        self.cells[addr] = (t, content)
        return addr

    def load(self, addr):
        if addr in self.cells:
            return self.cells[addr][1]
        assert self.allow_unwritten, "unwritten load in model W"
        return UNWRITTEN


class PathCopy:
    """F-ary trie of height h over [m], m = F^h. Node = F consecutive cells."""

    def __init__(self, m, F):
        self.m, self.F = m, F
        self.h = round(math.log(m, F))
        assert F ** self.h == m
        self.mem = Memory(allow_unwritten_loads=False)
        zero = self.mem.write(0, 0)
        a = zero
        for _ in range(self.h):
            base = None
            for k in range(F):
                c = self.mem.write(0, a)
                base = c if base is None else base
            a = base
        self.root = a          # the only register that matters
        self.writes_per_update = 1 + F * self.h

    def digits(self, i):
        d = []
        for _ in range(self.h):
            d.append(i % self.F)
            i //= self.F
        return d[::-1]       # most significant first

    def update(self, t, i, v):
        dig = self.digits(i)
        path = [self.root]
        for d in dig:
            path.append(self.mem.load(path[-1] + d))
        child = self.mem.write(t, v)
        for level in range(self.h - 1, -1, -1):
            old = path[level]
            base = None
            for k in range(self.F):
                c = child if k == dig[level] else self.mem.load(old + k)
                a = self.mem.write(t, c)
                base = a if base is None else base
            child = base
        self.root = child

    def reader(self, q, regs, load):
        """Pure reader: load(addr) returns content or raises Abort."""
        a = regs
        for d in self.digits(q):
            a = load(a + d)
        return load(a)


class Versioned:
    """Cell (i, k) at address i*K + k holds the k-th version (k >= 1).
    Loads unwritten cells (returns UNWRITTEN): outside model W."""

    def __init__(self, m, n):
        self.m, self.K = m, n + 2
        self.mem = Memory(allow_unwritten_loads=True)
        self.root = 0
        self.writes_per_update = 1

    def count_versions(self, i, load):
        lo, hi = 0, 1       # invariant: version lo written (lo=0 means none), find last
        while True:
            c = load(i * self.K + hi)
            if c is UNWRITTEN:
                break
            lo, hi = hi, hi * 2
        # last written version in [lo, hi)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if load(i * self.K + mid) is UNWRITTEN:
                hi = mid
            else:
                lo = mid
        return lo

    def update(self, t, i, v):
        k = self.count_versions(i, self.mem.load)
        self.mem.write(t, v, addr=i * self.K + k + 1)

    def reader(self, q, regs, load):
        k = self.count_versions(q, load)
        if k == 0:
            return 0
        return load(q * self.K + k)


class Abort(Exception):
    pass


def run(scheme_name, m, seed, B=2, F=2):
    rng = random.Random(seed)
    n = m
    if scheme_name == "PC":
        S = PathCopy(m, F)
    else:
        S = Versioned(m, n)
    ups = [(rng.randrange(m), rng.randrange(1, 2 ** W_BITS)) for _ in range(n)]
    for t, (i, v) in enumerate(ups, start=1):
        S.update(t, i, v)
    regs = S.root

    # probes of the real reader at every q (with write times)
    probe_times = []
    for q in range(m):
        times = []

        def ld(a, times=times):
            c = S.mem.cells.get(a)
            if c is None:
                times.append(None)
                return UNWRITTEN
            times.append(c[0])
            return c[1]
        S.reader(q, regs, ld)
        probe_times.append(times)
    mean_tq = sum(len(x) for x in probe_times) / m

    # epochs
    epochs = []
    lam_prev, j = 0, 1
    while True:
        lam = lam_prev + B ** j
        if lam > n:
            break
        epochs.append((j, n - lam, n - lam_prev))   # epoch = times in (lo, hi]
        lam_prev, j = lam, j + 1

    rows = []
    sum_beta = 0.0
    for (j, lo, hi) in epochs:
        # true quantities
        I_j = {ups[t - 1][0] for t in range(lo + 1, hi + 1)}
        P_j = {ups[t - 1][0] for t in range(hi + 1, n + 1)}
        A_pre = {}
        for t in range(1, lo + 1):
            A_pre[ups[t - 1][0]] = ups[t - 1][1]
        A_end = dict(A_pre)
        for t in range(lo + 1, hi + 1):
            A_end[ups[t - 1][0]] = ups[t - 1][1]
        # decoder knowledge: pre cells (time <= lo), post cells (time > hi), regs
        pre = {a: c for a, (tt, c) in S.mem.cells.items() if tt <= lo}
        post = {a: c for a, (tt, c) in S.mem.cells.items() if tt > hi}
        bad, good_out = [], {}
        aborted_in_epoch = True
        for q in range(m):
            def dl(a):
                if a in pre:
                    return pre[a]
                if a in post:
                    return post[a]
                raise Abort(a)
            try:
                good_out[q] = S.reader(q, regs, dl)
            except Abort as e:
                bad.append(q)
                a = e.args[0]
                cell = S.mem.cells.get(a)
                if cell is None or not (lo < cell[0] <= hi):
                    aborted_in_epoch = False
        bad_set = set(bad)
        # decoder reconstruction from good outputs
        rec = set()
        for q, out in good_out.items():
            if q in P_j:
                continue
            if out != A_pre.get(q, 0):
                rec.add(q)
        # encoder corrections (sent explicitly)
        coinc = {q for q in I_j - P_j if A_end[q] == A_pre.get(q, 0)}
        corr_bad = (I_j - P_j - coinc) & bad_set
        corr_P = I_j & P_j
        rec |= corr_bad | corr_P | coinc
        ok = rec == I_j
        # message length in bits
        n_post = len(post)
        k = len(corr_bad)
        msg = (W_BITS                                   # registers
               + math.ceil(math.log2(n_post + 2)) + 2 * W_BITS * n_post
               + math.ceil(math.log2(len(I_j) + 2))
               + log2binom(len(bad_set), k)
               + math.ceil(math.log2(len(I_j) + 2)) + log2binom(len(P_j), len(corr_P))
               + math.ceil(math.log2(len(I_j) + 2)) + len(coinc) * W_BITS)
        ent = log2binom(m, len(I_j))
        beta = len(bad_set) / m
        sum_beta += beta
        rows.append((j, B ** j, len(I_j), n_post, beta, ok, aborted_in_epoch, msg, ent))
    return mean_tq, sum_beta, rows, S.writes_per_update


def log2binom(a, b):
    if b < 0 or b > a:
        return float("inf")
    return (math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)) / math.log(2)


def main():
    mlog = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    m = 2 ** mlog
    all_ok = True
    for scheme, F in (("PC", 2), ("PC", 16), ("VA", None)):
        if scheme == "PC" and round(math.log(m, F)) != math.log(m, F):
            continue
        for seed in range(1, seeds + 1):
            mean_tq, sum_beta, rows, wpu = run(scheme, m, seed, B=2, F=F or 2)
            name = f"{scheme}(F={F})" if F else scheme
            print(f"{name} m={m} seed={seed} writes/update={wpu} mean_tq={mean_tq:.3f} "
                  f"sum_beta={sum_beta:.3f}")
            for (j, ell, sz, npost, beta, ok, inep, msg, ent) in rows:
                print(f"   j={j:2d} ell={ell:5d} |I_j|={sz:5d} post_cells={npost:6d} "
                      f"beta={beta:.3f} decode_ok={ok} aborts_in_epoch={inep} "
                      f"msg_bits={msg:9.0f} log2C(m,|I_j|)={ent:8.0f}")
                all_ok &= ok
                if scheme == "PC":
                    all_ok &= inep
            if scheme == "PC":
                all_ok &= sum_beta <= mean_tq + 1e-9
    print("ALL_W_CHECKS_PASS" if all_ok else "SOME_CHECK_FAILED")


if __name__ == "__main__":
    main()
