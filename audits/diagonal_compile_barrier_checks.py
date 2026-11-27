#!/usr/bin/env python3
"""Finite checks for notes/black-box-routes-through-the-diagonal-compile.md.

Part 1. The hard structure of the black-box model B0: Tseitin formulas with odd
        total charge on small 2-connected cubic graphs.  Checks by brute force:
        (a) the formula is UNSAT; (b) deleting any one clause makes it SAT;
        (c) replacing any one clause by any of the other 7 sign patterns on the
        same scope makes it SAT.  (c) is the adversary step of Theorem BB.
Part 2. Reference cost versus encoded length.  For Tseitin formulas on prism
        graphs C_m x K_2: K clauses, the ASCII DIMACS length M in bits, and the
        minimum total length sum_{j<=K} floor(log2 j) of K distinct binary
        clause references.  Prints the ratio.
Part 3. Switch counts.  Benes network on h = 2^m terminals uses h*m - h/2
        binary switches; the counting floor is log2(h!).  Prints the ratio.
Part 4. Route exponents.  log2(time / T) for the direct route (time ~ M =
        eps*T*log2 T) and for the V route with bit exponent b (time ~
        eps*T*log2^b T), at eps = log2(T)^(-theta).

No arguments.  No files written.  Run:  python3 diagonal_compile_barrier_checks.py   (about 3 s)
"""
import itertools
import math

import numpy as np


# ---------------------------------------------------------------- Part 1
def cubic_graphs():
    g = {}
    g["K4"] = (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
    # prism C3 x K2
    e = []
    for i in range(3):
        e += [(i, (i + 1) % 3), (3 + i, 3 + (i + 1) % 3), (i, 3 + i)]
    g["prism3"] = (6, e)
    # cube Q3
    e = [(a, a ^ (1 << k)) for a in range(8) for k in range(3) if a < a ^ (1 << k)]
    g["Q3"] = (8, e)
    # Petersen
    e = [(i, (i + 1) % 5) for i in range(5)]
    e += [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    e += [(i, 5 + i) for i in range(5)]
    g["Petersen"] = (10, e)
    return g


def tseitin(nv, edges, charge):
    """Clauses as (scope tuple of edge indices, forbidden pattern tuple)."""
    inc = [[] for _ in range(nv)]
    for idx, (a, b) in enumerate(edges):
        inc[a].append(idx)
        inc[b].append(idx)
    clauses = []
    for v in range(nv):
        sc = tuple(inc[v])
        assert len(sc) == 3
        for p in itertools.product((0, 1), repeat=3):
            if sum(p) % 2 != charge[v]:
                clauses.append((sc, p))  # forbids pattern p on scope sc
    return clauses


def sat_vector(nvars, scope, forbidden):
    a = np.arange(1 << nvars, dtype=np.int64)
    eq = np.ones(1 << nvars, dtype=bool)
    for var, bit in zip(scope, forbidden):
        eq &= ((a >> var) & 1) == bit
    return ~eq  # clause satisfied unless the assignment equals the forbidden pattern


def part1():
    print("Part 1: Tseitin structures (odd total charge), brute force")
    for name, (nv, edges) in cubic_graphs().items():
        ne = len(edges)
        charge = [1] + [0] * (nv - 1)
        cl = tseitin(nv, edges, charge)
        K = len(cl)
        vecs = [sat_vector(ne, sc, p) for sc, p in cl]
        pre = [np.ones(1 << ne, dtype=bool)]
        for v in vecs:
            pre.append(pre[-1] & v)
        suf = [np.ones(1 << ne, dtype=bool)]
        for v in reversed(vecs):
            suf.append(suf[-1] & v)
        suf = suf[::-1]
        unsat = not pre[-1].any()
        del_ok = all((pre[j] & suf[j + 1]).any() for j in range(K))
        flips = 0
        flip_ok = 0
        for j, (sc, p) in enumerate(cl):
            rest = pre[j] & suf[j + 1]
            for q in itertools.product((0, 1), repeat=3):
                if q == p:
                    continue
                flips += 1
                if (rest & sat_vector(ne, sc, q)).any():
                    flip_ok += 1
        print(f"  {name:9s} vertices={nv:2d} vars={ne:2d} clauses K={K:2d} "
              f"UNSAT={unsat} every-deletion-SAT={del_ok} "
              f"sign-changes SAT={flip_ok}/{flips}")
    print("Part 1b: hidden charges; SAT <=> charges have even parity, all charge vectors")
    for name, (nv, edges) in cubic_graphs().items():
        ne = len(edges)
        # per vertex and charge value, the AND of its 4 clause vectors
        inc = [[] for _ in range(nv)]
        for idx, (a, b) in enumerate(edges):
            inc[a].append(idx)
            inc[b].append(idx)
        local = []
        for v in range(nv):
            pair = []
            for c in (0, 1):
                acc = np.ones(1 << ne, dtype=bool)
                for p in itertools.product((0, 1), repeat=3):
                    if sum(p) % 2 != c:
                        acc &= sat_vector(ne, tuple(inc[v]), p)
                pair.append(acc)
            local.append(pair)
        agree = 0
        total = 0
        for chi in range(1 << nv):
            acc = np.ones(1 << ne, dtype=bool)
            for v in range(nv):
                acc &= local[v][(chi >> v) & 1]
            sat = bool(acc.any())
            total += 1
            agree += int(sat == (bin(chi).count("1") % 2 == 0))
        print(f"  {name:9s} charge vectors={total:5d} SAT==even-parity on {agree}/{total}")


# ---------------------------------------------------------------- Part 2
def dimacs_bits_prism(m):
    """ASCII DIMACS bit length of Tseitin(C_m x K_2), one clause per line."""
    nv, ne = 2 * m, 3 * m
    # edge numbering 1..ne: rim edges, second rim, spokes
    def dig(x):
        return len(str(x))
    # each vertex has 3 incident edges; 4 clauses per vertex; each clause has
    # 3 literals, 2 of them negated on average (patterns with fixed parity)
    total = 0
    inc = [[] for _ in range(nv)]
    eid = 0
    for i in range(m):
        for (a, b) in ((i, (i + 1) % m), (m + i, m + (i + 1) % m), (i, m + i)):
            eid += 1
            inc[a].append(eid)
            inc[b].append(eid)
    for v in range(nv):
        par = 1 if v == 0 else 0
        for p in itertools.product((0, 1), repeat=3):
            if sum(p) % 2 == par:
                continue
            line = 0
            for e, bit in zip(inc[v], p):
                line += dig(e) + (1 if bit == 1 else 0) + 1  # '-' if forbidden bit is 1, plus space
            line += 2  # "0\n"
            total += line
    header = len(f"p cnf {ne} {8 * m}\n")
    return 8 * (total + header), 8 * m


def ref_floor(K):
    return sum((j).bit_length() - 1 for j in range(1, K + 1))


def part2():
    print("Part 2: minimum reference cost sum_{j<=K} floor(log2 j) vs ASCII DIMACS bits M")
    for m in (10, 100, 1000, 10000, 100000):
        M, K = dimacs_bits_prism(m)
        R = ref_floor(K)
        P = (K // 4) * math.ceil(math.log2(K))  # parity adversary: |V| gates x ceil(log2 K) pins
        print(f"  m={m:6d} K={K:7d} M={M:10d} refs>={R:9d} refs/M={R / M:.4f} "
              f"log2(K!)-K={(math.lgamma(K + 1) / math.log(2) - K):.0f} "
              f"|V|*ceil(log2 K)={P} ratio={P / M:.4f}")


# ---------------------------------------------------------------- Part 3
def part3():
    print("Part 3: Benes switches h*log2(h) - h/2 vs counting floor log2(h!)")
    for mexp in (2, 3, 4, 8, 12, 16, 20):
        h = 1 << mexp
        benes = h * mexp - h // 2
        floor = math.lgamma(h + 1) / math.log(2)
        print(f"  h=2^{mexp:2d} benes={benes:10d} log2(h!)={floor:12.1f} ratio={benes / floor:.4f}")


# ---------------------------------------------------------------- Part 4
def part4():
    print("Part 4: log2(time/T) at eps = (log2 T)^(-theta); negative and decreasing = o(T)")
    print("  log2T   theta | direct(a=0) | V b=3 | V b=2 | V b=2.5")
    for L in (2 ** 10, 2 ** 20, 2 ** 40):
        for theta in (0.0, 0.5, 1.0, 1.5, 2.5, 3.5):
            lg = math.log2(L)
            direct = (1 - theta) * lg  # eps * log T
            v3 = (3 - theta) * lg
            v2 = (2 - theta) * lg
            v25 = (2.5 - theta) * lg
            print(f"  2^{int(lg):2d}  {theta:4.1f}  | {direct:8.1f}    | {v3:5.1f} | {v2:5.1f} | {v25:6.1f}")


# ---------------------------------------------------------------- Part 5
def part5(trials=20000, n=8, seed=1):
    """Sanity check of the parity adversary of Theorem BB.

    A query is a random DNF over n hidden bits whose terms have width <= g
    (one literal per opaque gate on a witness).  The adversary keeps a partial
    assignment P: YES if some term is consistent with P (and fixes it), else NO.
    Checks, over all completions of P: every reply equals the DNF's value, and
    the parity of the hidden bits is not determined while sum(g) < n.
    """
    import random
    rng = random.Random(seed)
    bad_reply = 0
    determined = 0
    for _ in range(trials):
        P = {}
        budget = n - 1
        history = []
        while budget > 0:
            g = rng.randint(1, budget)
            budget -= g
            nterms = rng.randint(1, 6)
            dnf = []
            for _t in range(nterms):
                vars_ = rng.sample(range(n), rng.randint(1, g))
                dnf.append({v: rng.randint(0, 1) for v in vars_})
            reply = False
            for term in dnf:
                if all(P.get(v, b) == b for v, b in term.items()):
                    reply = True
                    P.update(term)
                    break
            history.append((dnf, reply))
        free = [v for v in range(n) if v not in P]
        pars = set()
        for bits in itertools.product((0, 1), repeat=len(free)):
            x = dict(P)
            x.update(zip(free, bits))
            for dnf, reply in history:
                val = any(all(x[v] == b for v, b in term.items()) for term in dnf)
                if val != reply:
                    bad_reply += 1
            pars.add(sum(x.values()) % 2)
        if len(pars) < 2:
            determined += 1
    print(f"Part 5: parity adversary, n={n}, trials={trials}: "
          f"inconsistent replies={bad_reply}, parity determined={determined}")


if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
    part5()
