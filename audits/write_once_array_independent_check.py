#!/usr/bin/env python3
"""Independent check of the epoch decoders of Lemma A and Lemma A' of
notes/mutable-arrays-on-word-write-once-memory.md,
written during review from the note's text only (not from write_once_array_epoch_decoder_check.py).

Memory: write-once cells; each cell records (time, content).  A scheme in model W
must never load an unwritten cell; the VA scheme (outside W) may, and gets None.

Schemes (all deterministic):
  PC2      path copying, binary trie, root address in one register (W)
  PC4R     path copying, 4-ary trie; every read ALSO writes: it copies the read path
           with the same leaf value and moves the root (W; reads write cells, and the
           read loads back a cell it wrote itself)
  LOG      clock-addressed log: update t writes (i, v) at address BASE + t; a read
           scans back from the newest entry (W; t_u = 1, uses the public clock)
  LSM      Bentley-Saxe levels of sorted runs (newest wins), a directory block written
           fresh after every update, its address in one register; reads binary-search
           each level, newest first (W; amortized writes)
  VA       versioned addresses with galloping over unwritten cells (NOT in W)

Lemma A decoder (single read after n updates), epochs of B^j updates back from the end.
Lemma A' decoder (alternating update/read), epochs of B^j operations back from read T.
Checks for W schemes:
  (1) decoded I_j == true I_j
  (2) every abort is a load of a cell written inside the epoch (time in epoch window)
  (3) Bad_j == {q : the real read of q loads a cell written in epoch j}   (stronger)
  (4) sum_j |Bad_j| / m <= mean over q of the real read's load count
For VA, (2)-(4) are reported, expected to fail.

Usage: python3 write_once_array_independent_check.py [log2 m = 8] [seeds = 2] [value bits = 32]
"""
import random
import sys


class Abort(Exception):
    pass


class Mem:
    def __init__(self, w_model=True):
        self.c = {}
        self.nxt = 1 << 40           # bump allocator far from fixed regions
        self.w_model = w_model

    def wr(self, t, val, addr=None):
        if addr is None:
            addr = self.nxt
            self.nxt += 1
        assert addr not in self.c, ("rewrite", addr)
        self.c[addr] = (t, val)
        return addr

    def alloc(self, k):
        a = self.nxt
        self.nxt += k
        return a


# ---------------------------------------------------------------- schemes
# Each scheme: init(mem) -> regs ; update(mem, t, regs, i, v) -> regs (loads free)
# read(env, regs, q) -> (answer, new_regs)   where env.ld(a), env.wr(val[,addr])


class PathCopy:
    def __init__(self, m, F, reads_write):
        self.m, self.F, self.rw = m, F, reads_write
        self.h = 0
        while F ** self.h < m:
            self.h += 1
        assert F ** self.h == m
        self.name = f"PC{F}" + ("R" if reads_write else "")

    def digits(self, i):
        out = []
        for _ in range(self.h):
            out.append(i % self.F)
            i //= self.F
        return out[::-1]

    def init(self, mem):
        a = mem.wr(0, 0)
        for _ in range(self.h):
            base = mem.alloc(self.F)
            for k in range(self.F):
                mem.wr(0, a, base + k)
            a = base
        return a

    def update(self, mem, t, root, i, v):
        dig = self.digits(i)
        nodes = [root]
        for d in dig:
            nodes.append(mem.c[nodes[-1] + d][1])
        child = mem.wr(t, v)
        for lev in range(self.h - 1, -1, -1):
            base = mem.alloc(self.F)
            for k in range(self.F):
                val = child if k == dig[lev] else mem.c[nodes[lev] + k][1]
                mem.wr(t, val, base + k)
            child = base
        return child

    def read(self, env, root, q):
        dig = self.digits(q)
        nodes = [root]
        for d in dig:
            nodes.append(env.ld(nodes[-1] + d))
        val = env.ld(nodes[-1])
        if not self.rw:
            return val, root
        # read also writes: copy the path (same leaf value), load the new leaf back
        leaf = env.wr(val)
        child = leaf
        for lev in range(self.h - 1, -1, -1):
            base = env.alloc(self.F)
            for k in range(self.F):
                cv = child if k == dig[lev] else env.ld(nodes[lev] + k)
                env.wr(cv, base + k)
            child = base
        again = env.ld(leaf)          # load of a cell the read itself wrote
        assert again == val
        return val, child


class LogScan:
    name = "LOG"
    BASE = 1 << 20

    def __init__(self, m):
        self.m = m

    def init(self, mem):
        return 0                       # register = number of updates so far

    def update(self, mem, t, cnt, i, v):
        cnt += 1
        mem.wr(t, (i, v), self.BASE + cnt)
        return cnt

    def read(self, env, cnt, q):
        for k in range(cnt, 0, -1):
            i, v = env.ld(self.BASE + k)
            if i == q:
                return v, cnt
        return 0, cnt


class LSM:
    """levels L_0..L_K; level k holds a sorted run of distinct keys (newest values),
    at most 2^k keys; directory block (K+1 cells: (addr, len) per level) written
    fresh after every update; register = directory address."""
    name = "LSM"

    def __init__(self, m, K=24):
        self.m, self.K = m, K

    def init(self, mem):
        d = mem.alloc(self.K + 1)
        for k in range(self.K + 1):
            mem.wr(0, (0, 0), d + k)
        return d

    def update(self, mem, t, d, i, v):
        runs = [mem.c[d + k][1] for k in range(self.K + 1)]
        carry = {i: v}                 # newest first semantics: carry is newer
        k = 0
        while runs[k][1] > 0:
            a, ln = runs[k]
            for p in range(ln):
                key, val = mem.c[a + p][1]
                if key not in carry:
                    carry[key] = val
            runs[k] = (0, 0)
            k += 1
        keys = sorted(carry)
        a = mem.alloc(len(keys))
        for p, key in enumerate(keys):
            mem.wr(t, (key, carry[key]), a + p)
        runs[k] = (a, len(keys))
        nd = mem.alloc(self.K + 1)
        for kk in range(self.K + 1):
            mem.wr(t, runs[kk], nd + kk)
        return nd

    def read(self, env, d, q):
        for k in range(self.K + 1):
            a, ln = env.ld(d + k)
            lo, hi = 0, ln
            while lo < hi:
                mid = (lo + hi) // 2
                key, val = env.ld(a + mid)
                if key == q:
                    return val, d
                if key < q:
                    lo = mid + 1
                else:
                    hi = mid
        return 0, d


class VA:
    name = "VA"

    def __init__(self, m, n):
        self.m, self.K = m, n + 2

    def init(self, mem):
        return 0

    def _last(self, ld, q):
        lo, hi = 0, 1
        while ld(q * self.K + hi) is not None:
            lo, hi = hi, 2 * hi
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ld(q * self.K + mid) is None:
                hi = mid
            else:
                lo = mid
        return lo

    def update(self, mem, t, r, i, v):
        k = self._last(lambda a: mem.c[a][1] if a in mem.c else None, i)
        mem.wr(t, v, i * self.K + k + 1)
        return r

    def read(self, env, r, q):
        k = self._last(env.ld, q)
        return (0 if k == 0 else env.ld(q * self.K + k)), r


# ---------------------------------------------------------------- environments

class RealEnv:
    """Runs a read against the real memory (writes go to a private overlay)."""

    def __init__(self, mem, t, w_model):
        self.mem, self.t, self.w = mem, t, w_model
        self.own = {}
        self.nxt = mem.nxt + (1 << 30)
        self.loads = []                # write time of each loaded cell (None = unwritten)

    def alloc(self, k):
        a = self.nxt
        self.nxt += k
        return a

    def wr(self, val, addr=None):
        if addr is None:
            addr = self.alloc(1)
        assert addr not in self.mem.c and addr not in self.own
        self.own[addr] = val
        return addr

    def ld(self, a):
        if a in self.own:
            self.loads.append(self.t)
            return self.own[a]
        if a in self.mem.c:
            self.loads.append(self.mem.c[a][0])
            return self.mem.c[a][1]
        assert not self.w, "unwritten load by a model-W scheme"
        self.loads.append(None)
        return None


class DecEnv(RealEnv):
    """Decoder's simulation: knows cells with time <= lo or in post window; aborts
    on any other address (including unwritten ones)."""

    def __init__(self, mem, t, lo, post_lo, post_hi, base_nxt):
        self.mem, self.t = mem, t
        self.lo, self.plo, self.phi = lo, post_lo, post_hi
        self.own = {}
        self.nxt = base_nxt
        self.loads = []

    def wr(self, val, addr=None):
        if addr is None:
            addr = self.alloc(1)
        self.own[addr] = val
        return addr

    def ld(self, a):
        if a in self.own:
            return self.own[a]
        cell = self.mem.c.get(a)
        if cell is not None:
            tt = cell[0]
            if tt <= self.lo or self.plo < tt <= self.phi:
                return cell[1]
        raise Abort(a)


# ---------------------------------------------------------------- runs

def epochs_back(B, span):
    """list of (j, a, b): epoch j = offsets (a, b] back from the reference point,
    i.e. times in (ref - b, ref - a]."""
    out, lam_prev, j = [], 0, 1
    while lam_prev + B ** j <= span:
        out.append((j, lam_prev, lam_prev + B ** j))
        lam_prev += B ** j
        j += 1
    return out


def check_one_read(scheme, mem, regs, t_read, upd_log, B, m, w_model, span, ref=None):
    """upd_log: list of (time, i, v) of updates before t_read (time-ordered).
    Returns dict of results for the read at time t_read from registers regs."""
    # real reads for every q
    real_answer, real_times, cost = {}, {}, {}
    for q in range(m):
        env = RealEnv(mem, t_read, w_model)
        ans, _ = scheme.read(env, regs, q)
        real_answer[q] = ans
        real_times[q] = env.loads
        cost[q] = len(env.loads)
    # true array
    A = {}
    for (tt, i, v) in upd_log:
        A[i] = v
    for q in range(m):
        assert real_answer[q] == A.get(q, 0), (scheme.name, "wrong answer", q)
    mean_cost = sum(cost.values()) / m
    res = {"mean_cost": mean_cost, "epochs": []}
    if ref is None:
        ref = t_read - 1                 # Lemma A: epochs end at the last update
    last = t_read - 1                    # post window ends at the last operation before the read
    for (j, a, b) in epochs_back(B, span):
        lo, hi = ref - b, ref - a        # epoch = times in (lo, hi]
        if lo < 0:
            break
        I = {i for (tt, i, v) in upd_log if lo < tt <= hi}
        P = {i for (tt, i, v) in upd_log if tt > hi}
        Apre = {}
        for (tt, i, v) in upd_log:
            if tt <= lo:
                Apre[i] = v
        Aend = dict(Apre)
        for (tt, i, v) in upd_log:
            if lo < tt <= hi:
                Aend[i] = v
        bad, good = set(), {}
        abort_ok = True
        for q in range(m):
            env = DecEnv(mem, t_read, lo, hi, last, mem.nxt + (1 << 30))
            try:
                ans, _ = scheme.read(env, regs, q)
                good[q] = ans
            except Abort as e:
                bad.add(q)
                cell = mem.c.get(e.args[0])
                if cell is None or not (lo < cell[0] <= hi):
                    abort_ok = False
        # decoder reconstruction
        rec = {q for q, ans in good.items() if q not in P and ans != Apre.get(q, 0)}
        n_from_good = len(rec)
        C = {q for q in I - P if Aend[q] == Apre.get(q, 0)}
        rec |= ((I - P - C) & bad) | (I & P) | C
        # mutation controls: dropping a correction field must break decoding when used
        drop_P_breaks = (rec - ((I & P) - ((I - P - C) & bad) - C)) != I if (I & P) else None
        touch = {q for q in range(m)
                 if any(x is not None and lo < x <= hi for x in real_times[q])}
        res["epochs"].append({
            "j": j, "ell": b - a, "I": len(I), "beta": len(bad) / m,
            "decode_ok": rec == I, "abort_in_epoch": abort_ok,
            "bad_eq_touch": bad == touch,
            "k_good": n_from_good, "k_bad": len((I - P - C) & bad), "k_P": len(I & P),
            "k_C": len(C), "drop_P_breaks": drop_P_breaks,
            "post_cells": sum(1 for (tt, _) in mem.c.values() if hi < tt <= last),
        })
    res["sum_beta"] = sum(e["beta"] for e in res["epochs"])
    return res


def make(name, m, n):
    if name == "PC2":
        return PathCopy(m, 2, False), True
    if name == "PC4R":
        return PathCopy(m, 4, True), True
    if name == "LOG":
        return LogScan(m), True
    if name == "LSM":
        return LSM(m), True
    if name == "VA":
        return VA(m, n), False
    raise ValueError(name)


def lemma_A(name, m, seed, B):
    rng = random.Random(1000 * seed + 7)
    n = m
    scheme, wm = make(name, m, n)
    mem = Mem(wm)
    regs = scheme.init(mem)
    log = []
    for t in range(1, n + 1):
        i, v = rng.randrange(m), rng.randrange(1, 1 << VBITS)
        regs = scheme.update(mem, t, regs, i, v)
        log.append((t, i, v))
    return check_one_read(scheme, mem, regs, n + 1, log, B, m, wm, n)


def lemma_A_prime(name, m, seed, B, n_ops, n_T):
    """alternating: odd times update, even times read.  Reads are run for real (they
    may write cells and move registers).  For n_T read times T in the second half,
    the decoder of A' is checked from the registers after T-1."""
    rng = random.Random(2000 * seed + 11)
    scheme, wm = make(name, m, n_ops)
    mem = Mem(wm)
    regs = scheme.init(mem)
    log = []
    Ts = sorted(rng.sample(range(n_ops // 2 + (n_ops // 2) % 2 + 2, n_ops + 1, 2), n_T))
    results = []
    for t in range(1, n_ops + 1):
        if t % 2 == 1:
            i, v = rng.randrange(m), rng.randrange(1, 1 << VBITS)
            regs = scheme.update(mem, t, regs, i, v)
            log.append((t, i, v))
        else:
            if t in Ts:
                results.append((t, check_one_read(scheme, mem, regs, t, list(log), B,
                                                  m, wm, t - 1, ref=t)))
            q = rng.randrange(m)
            env = RealEnv(mem, t, wm)
            # commit the real read's writes to memory
            ans, new_regs = scheme.read(env, regs, q)
            for a, val in env.own.items():
                mem.wr(t, val, a)
            mem.nxt = max(mem.nxt, env.nxt)
            regs = new_regs
    return results


VBITS = int(sys.argv[3]) if len(sys.argv) > 3 else 32
FIELD = {'epochs': 0, 'good>0': 0, 'bad>0': 0, 'P>0': 0, 'C>0': 0, 'dropP_breaks': 0, 'dropP_harmless': 0}


def main():
    mlog = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    m = 1 << mlog
    allok = True
    count = {"decode_ok": 0, "decode_bad": 0}
    print(f"# Lemma A decoder, m={m}, n=m, B=2 and B=3")
    for name in ("PC2", "PC4R", "LOG", "LSM", "VA"):
        if name == "PC4R" and mlog % 2:
            continue
        for B in (2, 3):
            for seed in range(1, seeds + 1):
                r = lemma_A(name, m, seed, B)
                eps = r["epochs"]
                dec = all(e["decode_ok"] for e in eps)
                ab = all(e["abort_in_epoch"] for e in eps)
                eq = all(e["bad_eq_touch"] for e in eps)
                ineq = r["sum_beta"] <= r["mean_cost"] + 1e-12
                for e in eps:
                    FIELD["epochs"] += 1
                    FIELD["good>0"] += e["k_good"] > 0
                    FIELD["bad>0"] += e["k_bad"] > 0
                    FIELD["P>0"] += e["k_P"] > 0
                    FIELD["C>0"] += e["k_C"] > 0
                    FIELD["dropP_breaks"] += e["drop_P_breaks"] is True
                    FIELD["dropP_harmless"] += e["drop_P_breaks"] is False
                count["decode_ok"] += sum(e["decode_ok"] for e in eps)
                count["decode_bad"] += sum(not e["decode_ok"] for e in eps)
                print(f"A  {name:5s} B={B} seed={seed} epochs={len(eps):2d} mean_cost={r['mean_cost']:8.3f} "
                      f"sum_beta={r['sum_beta']:7.3f} decode_all={dec} aborts_in_epoch={ab} "
                      f"bad==touch={eq} sum_beta<=cost={ineq}")
                allok &= dec
                if name != "VA":
                    allok &= ab and eq and ineq
    print(f"# Lemma A' decoder (alternating), m={m}, n_ops=2m, B=2, 6 read times per run")
    for name in ("PC2", "PC4R", "LSM", "LOG", "VA"):
        if name == "PC4R" and mlog % 2:
            continue
        for seed in range(1, seeds + 1):
            res = lemma_A_prime(name, m, seed, 2, 2 * m, 6)
            for (T, r) in res:
                eps = r["epochs"]
                dec = all(e["decode_ok"] for e in eps)
                ab = all(e["abort_in_epoch"] for e in eps)
                eq = all(e["bad_eq_touch"] for e in eps)
                ineq = r["sum_beta"] <= r["mean_cost"] + 1e-12
                for e in eps:
                    FIELD["epochs"] += 1
                    FIELD["good>0"] += e["k_good"] > 0
                    FIELD["bad>0"] += e["k_bad"] > 0
                    FIELD["P>0"] += e["k_P"] > 0
                    FIELD["C>0"] += e["k_C"] > 0
                    FIELD["dropP_breaks"] += e["drop_P_breaks"] is True
                    FIELD["dropP_harmless"] += e["drop_P_breaks"] is False
                count["decode_ok"] += sum(e["decode_ok"] for e in eps)
                count["decode_bad"] += sum(not e["decode_ok"] for e in eps)
                print(f"A' {name:5s} seed={seed} T={T:5d} epochs={len(eps):2d} mean_cost={r['mean_cost']:8.3f} "
                      f"sum_beta={r['sum_beta']:7.3f} decode_all={dec} aborts_in_epoch={ab} "
                      f"bad==touch={eq} sum_beta<=cost={ineq}")
                allok &= dec
                if name != "VA":
                    allok &= ab and eq and ineq
    print(f"# epoch decodes: ok={count['decode_ok']} failed={count['decode_bad']}")
    print(f"# field usage over all epochs: {FIELD}")
    print("INDEPENDENT_W_CHECKS_PASS" if allok else "INDEPENDENT_SOME_CHECK_FAILED")


if __name__ == "__main__":
    main()
