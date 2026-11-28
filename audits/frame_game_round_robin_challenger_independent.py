#!/usr/bin/env python3
"""Independent check, written during review, of the Challenger sigma of notes/frame-value-on-round-robin-ladders.md
(written from its Section 3 only).
Run from audits/: python3 frame_game_round_robin_challenger_independent.py [C,T ...]
With no argument it runs the non-vacuous list 1,4 1,8 2,3 2,4 2,5 2,6 2,7 3,4 3,5 3,6 4,5 (about a second); the
review's second list is 2,8 2,9 2,10 2,11 2,12 3,7 3,8 3,9 4,6 4,7 1,16 1,33 (about 4 minutes). Exits 1 on a
violation. Nothing is written.

- frame DAG built from the definition (cone of S_T; node (mu,c) = version(c,mu); preds (mu-1,c), S_{mu-1});
- sigma with tie-breaking different from frame_game_round_robin_challenger.cpp: B by greedy removal in DESCENDING index order
  (variant 'desc') or ascending ('asc'); v chosen as the LARGEST index ('max') or smallest ('min');
- exhaustive Pebbler (BFS, any unpebbled node) -> Pstar(sigma);
- own exact DT value V (memoised minimax) where small enough;
- own recursion g (the note's Section 5) and closed form G = C log2((L+C)/(4C)).
Asserts: p in B, Lemma 5 strong form inside the focus, (A)/(B), I(R') after rule 1, rule 2 only with p not in R,
Fact 1, jump with a=1 only when L <= C; and finally g(T) <= Pstar <= V.
"""
import sys, math
from functools import lru_cache
from collections import deque


def frame_dag(addr):
    """addr[1..T] (addr[0] unused). Returns nodes list [(mu,c)], preds bitmasks, layer, cell, sink index."""
    T = len(addr) - 1
    def version(c, mu):
        return (mu, c)
    # backward search from S_T = (T, addr[T])
    sink = (T, addr[T])
    cone = {sink}
    stack = [sink]
    while stack:
        mu, c = stack.pop()
        if mu >= 2:
            for q in ((mu - 1, c), (mu - 1, addr[mu - 1])):
                if q not in cone:
                    cone.add(q); stack.append(q)
    nodes = sorted(cone)  # by layer then cell: topological
    idx = {v: i for i, v in enumerate(nodes)}
    preds = []
    for (mu, c) in nodes:
        m = 0
        if mu >= 2:
            m |= 1 << idx[(mu - 1, c)]
            m |= 1 << idx[(mu - 1, addr[mu - 1])]
        preds.append(m)
    return nodes, preds, idx[sink]


class Game:
    def __init__(self, addr, C, bvar='desc', vvar='max'):
        self.addr = addr; self.C = C; self.T = len(addr) - 1
        self.nodes, self.preds, self.sink = frame_dag(addr)
        self.n = len(self.nodes)
        self.lay = [mu for (mu, c) in self.nodes]
        self.cel = [c for (mu, c) in self.nodes]
        self.anc = [0] * self.n
        for i in range(self.n):
            m = self.preds[i]
            a = m
            j = 0
            while m:
                if m & 1:
                    a |= self.anc[j]
                m >>= 1; j += 1
            self.anc[i] = a
        self.laymask = {}
        for i in range(self.n):
            self.laymask[self.lay[i]] = self.laymask.get(self.lay[i], 0) | (1 << i)
        self.bvar = bvar; self.vvar = vvar
        self.stats = dict(r1a_stay=0, r1a_jump=0, r1b=0, nofocus=0, r2=0, r3=0, asserts=0)

    def R(self, vR, s):
        m = self.anc[vR] | (1 << vR)
        out = 0
        for i in range(self.n):
            if (m >> i) & 1 and self.lay[i] >= s:
                out |= 1 << i
        return out

    def is_open(self, Peb, vR, s):
        R = self.R(vR, s)
        reach = 0
        for i in range(self.n):
            if not (R >> i) & 1 or (Peb >> i) & 1:
                continue
            if self.lay[i] == s or (self.preds[i] & reach):
                reach |= 1 << i
        return (reach >> vR) & 1 == 1

    def link(self, Peb, vR, uc):
        if uc == vR:
            return not (Peb >> vR) & 1
        if (Peb >> vR) & 1:
            return False
        reach = 1 << vR  # unpebbled nodes reachable from vR along unpebbled nodes
        for i in range(vR + 1, self.n):
            if self.preds[i] & reach:
                if i == uc:
                    return True
                if not (Peb >> i) & 1:
                    reach |= 1 << i
        return False

    def game_over(self, P, uc):
        return (self.preds[uc] & ~P) == 0

    def answer(self, P, st, p):
        """st = (uc, vR, s) with vR = -1 meaning no focus. Returns new st."""
        uc, vR, s = st
        P2 = P | (1 << p)
        if vR < 0:
            return (uc, vR, s)
        C = self.C
        R = self.R(vR, s)
        top = self.lay[vR]; L = top - s + 1
        if (R >> p) & 1 and not self.is_open(P2, vR, s):
            # rule 1
            B = P2 & R
            order = range(self.n - 1, -1, -1) if self.bvar == 'desc' else range(self.n)
            for i in order:
                if (B >> i) & 1 and not self.is_open(B & ~(1 << i), vR, s):
                    B &= ~(1 << i)
            # minimality check
            for i in range(self.n):
                if (B >> i) & 1:
                    assert self.is_open(B & ~(1 << i), vR, s), "B not minimal"
            assert not self.is_open(B, vR, s)
            assert (B >> p) & 1, "p not in B"
            self.stats['asserts'] += 1
            Bl = [i for i in range(self.n) if (B >> i) & 1]
            a = min(self.lay[i] for i in Bl); b = max(self.lay[i] for i in Bl)
            # Lemma 5 strong form inside focus: cell accessed at focus layer mu (s<=mu<=top) is addr[mu]
            # for mu < top, and cel[vR] at mu = top.
            def acc(mu):
                return self.cel[vR] if mu == top else self.addr[mu]
            lam = {}
            for mu in range(a, top + 1):
                lam.setdefault(acc(mu), mu)
            seen = set()
            for i in Bl:
                c = self.cel[i]
                assert c in lam, "B node on a column not accessed in [a, top]"
                assert c not in seen, "two B nodes on one column"
                seen.add(c)
                assert self.lay[i] <= lam[c], "B node above lambda_c"
            assert len(Bl) == len(lam), "|B| != #cells"
            arel = a - s + 1; brel = b - s + 1
            x = len(Bl)
            if arel <= L - C:
                assert x == C, "(A) |B| != C"
                assert brel - arel + 1 <= C, "(A) spread > C"
                jump = arel + brel > L
                self.stats['r1a_jump' if jump else 'r1a_stay'] += 1
            else:
                assert L - arel <= x <= L - arel + 1 and 1 <= x <= C, "(B) violated"
                jump = True
                self.stats['r1b'] += 1
            if not jump:
                s2 = b + 1
                assert s2 <= top
                assert self.is_open(P2, vR, s2), "stay focus not open"
                assert self.link(P2, vR, uc), "stay: link broken"
                return (uc, vR, s2)
            if a - 1 < s:
                assert L <= C, "jump with a = 1 but L > C"
                self.stats['nofocus'] += 1
                return (p, -1, s)
            # v: layer a-1 node of an open (w.r.t. old P) path Q from layer s through p
            fwd = 0
            for i in range(self.n):
                if not (R >> i) & 1 or (P >> i) & 1:
                    continue
                if self.lay[i] == s or (self.preds[i] & fwd):
                    fwd |= 1 << i
            bwd = 1 << p  # nodes with an old-P-free path to p (p itself is unpebbled in P)
            for i in range(p - 1, -1, -1):
                if not (R >> i) & 1 or (P >> i) & 1:
                    continue
                # successors of i inside bwd?
                for j in range(i + 1, self.n):
                    if (bwd >> j) & 1 and (self.preds[j] >> i) & 1:
                        bwd |= 1 << i
                        break
            cand = [i for i in range(self.n) if (fwd >> i) & 1 and (bwd >> i) & 1 and self.lay[i] == a - 1]
            assert cand, "no v"
            v = max(cand) if self.vvar == 'max' else min(cand)
            assert self.is_open(P2, v, s), "jump focus not open"
            assert self.link(P2, v, p), "jump: no link"
            Rn = self.R(v, s)
            assert Rn & ~R == 0 and Rn & B == 0, "nesting"
            return (p, v, s)
        if not self.link(P2, vR, uc):
            assert not (R >> p) & 1, "rule 2 with p in R"
            assert self.link(P2, vR, p), "rule 2: no link to p"
            self.stats['r2'] += 1
            return (p, vR, s)
        self.stats['r3'] += 1
        return (uc, vR, s)

    def check_inv(self, P, st):
        uc, vR, s = st
        if vR < 0:
            return
        assert self.is_open(P, vR, s), "I(R): not open"
        assert self.link(P, vR, uc), "I(R): no link"
        L = self.lay[vR] - s + 1
        if L >= 2:
            assert not self.game_over(P, uc), "Fact 1 violated"

    def pstar(self, cap_depth=40, max_states=3_000_000):
        st0 = (self.sink, self.sink, 1)
        start = (0, st0)
        if self.game_over(0, self.sink):
            return 0, 1
        seen = {start}
        frontier = [start]
        depth = 0
        while frontier:
            depth += 1
            nxt = []
            for (P, st) in frontier:
                for p in range(self.n):
                    if (P >> p) & 1:
                        continue
                    st2 = self.answer(P, st, p)
                    P2 = P | (1 << p)
                    self.check_inv(P2, st2)
                    if self.game_over(P2, st2[0]):
                        return depth, len(seen)
                    key = (P2, st2)
                    if key not in seen:
                        seen.add(key); nxt.append(key)
                        if len(seen) > max_states:
                            return None, len(seen)
            frontier = nxt
            if depth >= cap_depth:
                return None, len(seen)
        return math.inf, len(seen)

    def exact_V(self):
        n = self.n
        preds = self.preds; anc = self.anc
        sys.setrecursionlimit(100000)
        @lru_cache(maxsize=None)
        def val(P, u):
            P &= anc[u]
            if preds[u] & ~P == 0:
                return 0
            best = math.inf
            m = anc[u] & ~P
            i = 0
            while m:
                if m & 1:
                    P2 = P | (1 << i)
                    v = 1 + max(val(P2 & anc[u], u), val(P2 & anc[i], i))
                    if v < best:
                        best = v
                m >>= 1; i += 1
            return best
        return val(0, self.sink)


def grec(C, Lmax):
    g = [0] * (Lmax + 1)
    for L in range(2, Lmax + 1):
        opts = []
        for a in range(1, L - C + 1):
            for d in range(1, C + 1):
                b = a + d - 1
                if b >= L:
                    continue
                opts.append(C + max(g[L - b], g[a - 1]))
        for a in range(max(1, L - C + 1), L + 1):
            opts.append(max(1, L - a) + g[a - 1])
        g[L] = min(opts)
    return g


def main():
    sizes = []
    for spec in sys.argv[1:] or '1,4 1,8 2,3 2,4 2,5 2,6 2,7 3,4 3,5 3,6 4,5'.split():
        C, T = map(int, spec.split(','))
        sizes.append((C, T))
    bad = 0
    for (C, T) in sizes:
        addr = [None] + [(t - 1) % C for t in range(1, T + 1)]
        g = grec(C, T)[T]
        line = []
        for bvar, vvar in (('desc', 'max'), ('asc', 'min')):
            G = Game(addr, C, bvar, vvar)
            ps, ns = G.pstar()
            line.append((bvar, vvar, ps, ns, dict(G.stats)))
        G0 = Game(addr, C)
        V = G0.exact_V() if G0.n <= 15 else None
        Gc = max(0.0, C * math.log2((T + C) / (4 * C)))
        for (bvar, vvar, ps, ns, stats) in line:
            ok = ps is not None and g <= ps and (V is None or ps <= V) and Gc <= g + 1e-9
            bad += not ok
            print(f"C={C} T={T} n={G0.n} [{bvar},{vvar}] g={g} G+={Gc:.2f} Pstar={ps} V={V} states={ns} "
                  f"r1a_stay={stats['r1a_stay']} r1a_jump={stats['r1a_jump']} r1b={stats['r1b']} nofocus={stats['nofocus']} "
                  f"r2={stats['r2']} r3={stats['r3']} {'ok' if ok else 'VIOLATION'}", flush=True)
    print(f"violations {bad}")
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
