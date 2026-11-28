#!/usr/bin/env python3
"""Checks D1 and D2 for notes/the-price-inequality-and-its-table-reading-dual-cannot-certify-more-than-n-log-n.md:
the cut-rank measures against true minimum networks, at the only sizes where exact minima are computable.

D1  census of genuine fixed-B slices P_B (|B| = n = 4, B+B not a subspace, P_B not constant)
    at w = 3, 4: the smallest genuine non-subspace slice has N = n*w = 16 input bits.
D2  exhaustive minimum exact F_2-networks with 4 legs: every topology with V <= 5 vertices of
    arity <= 3 (legs attached to vertices, no self-loops, every component touching a leg), tables
    found by CaDiCaL.  For each target f this gives V*(f) = min #vertices of an exact network, and
    the certified values of the two cut-rank price methods:
      LB_primal(f) = min #vertices of a topology passing every edge-cut inequality
                     (crossing edges >= log2 rank_f across the induced leg split),
      LB_dual(f)   = min #vertices of a topology passing every vertex-split inequality with
                     all-GHZ tables (#split vertices >= log2 rank_f).
    Soundness requires LB <= V*.
CaDiCaL is found on PATH or in a Lean toolchain; its CNF files go to a temporary directory.
Usage: python3 -B four_leg_minimum_networks.py [VMAX]   (default 5, about 40 s)
"""
import itertools
import math
import os
import random
import subprocess
import sys
import tempfile

import numpy as np

from pathlib import Path


def find_cadical():
    from shutil import which
    found = which("cadical")
    if found:
        return found
    candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
    if candidates:
        return str(candidates[0])
    raise SystemExit("cadical not found: put it on PATH or install a Lean toolchain")


CADICAL = find_cadical()
random.seed(7)


def is_subspace(S):
    S = set(S)
    return all((a ^ b) in S for a in S for b in S)


def d1():
    print("D1: genuine fixed-B slices with n = 4 records")
    for w in (3, 4):
        pts = list(range(2 ** w))
        quads = list(itertools.combinations(pts, 4))
        tot = nonsub = nonconst_nonsub = nonconst_sub = 0
        for B in quads:
            S = {a ^ b for a in B for b in B}
            sub = is_subspace(S)
            tot += 1
            # P_B not identically zero iff some 4-set A has all pairwise xors outside S
            nz = any(all((A[i] ^ A[k]) not in S for i in range(4) for k in range(i + 1, 4)) for A in quads)
            if not sub:
                nonsub += 1
                nonconst_nonsub += nz
            else:
                nonconst_sub += nz
        print(f"  w={w}: 4-sets B={tot}  B+B not a subspace={nonsub}  of these with P_B not identically 0="
              f"{nonconst_nonsub}  (subspace sumsets with P_B not identically 0={nonconst_sub});  N = 4w = {4 * w}")


# ------------------------------------------------------------------ topologies
def topologies(V, N=4):
    """All multigraphs on V vertices, N labelled legs, degree <= 3, no self loops, each component
    touches a leg, every vertex degree >= 1; up to vertex relabelling."""
    seen = set()
    out = []
    pairs = [(u, v) for u in range(V) for v in range(u + 1, V)]
    for legmap in itertools.product(range(V), repeat=N):
        cap = [3] * V
        for v in legmap:
            cap[v] -= 1
        if min(cap) < 0:
            continue

        def rec(k, cap, edges):
            if k == len(pairs):
                yield list(edges)
                return
            u, v = pairs[k]
            for m in range(0, min(cap[u], cap[v]) + 1):
                cap[u] -= m
                cap[v] -= m
                edges.extend([(u, v)] * m)
                yield from rec(k + 1, cap, edges)
                for _ in range(m):
                    edges.pop()
                cap[u] += m
                cap[v] += m
        for edges in rec(0, cap[:], []):
            deg = [0] * V
            for v in legmap:
                deg[v] += 1
            for u, v in edges:
                deg[u] += 1
                deg[v] += 1
            if min(deg) == 0:
                continue
            # components touch a leg
            par = list(range(V))

            def find(a):
                while par[a] != a:
                    par[a] = par[par[a]]
                    a = par[a]
                return a
            for u, v in edges:
                par[find(u)] = find(v)
            legroots = {find(v) for v in legmap}
            if any(find(v) not in legroots for v in range(V)):
                continue
            # skip vertices of degree 2 with no leg?  (they are matrices; keep: they may be needed? no:
            # an arity-2 vertex on an internal edge can be absorbed, but keep for completeness)
            key = None
            for perm in itertools.permutations(range(V)):
                k2 = (tuple(perm[v] for v in legmap), tuple(sorted(tuple(sorted((perm[u], perm[v]))) for u, v in edges)))
                if key is None or k2 < key:
                    key = k2
            if key in seen:
                continue
            seen.add(key)
            out.append((list(key[0]), list(key[1])))
    return out


# ------------------------------------------------------------------ measures
def frank2(f, rows):
    """rank over F_2 of the flattening of f (dict x->bit over 4 legs) with legs 'rows' as row index."""
    N = 4
    cols = [i for i in range(N) if i not in rows]
    M = []
    for r in itertools.product((0, 1), repeat=len(rows)):
        row = 0
        for c in itertools.product((0, 1), repeat=len(cols)):
            x = [0] * N
            for i, b in zip(rows, r):
                x[i] = b
            for i, b in zip(cols, c):
                x[i] = b
            row = (row << 1) | f[tuple(x)]
        M.append(row)
    # gaussian elimination on bit rows
    rank = 0
    M = [m for m in M]
    width = 2 ** len(cols)
    for bit in reversed(range(width)):
        piv = next((i for i in range(rank, len(M)) if M[i] >> bit & 1), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        for i in range(len(M)):
            if i != rank and M[i] >> bit & 1:
                M[i] ^= M[rank]
        rank += 1
    return rank


def need_table(f):
    need = {}
    for mask in range(16):
        rows = [i for i in range(4) if mask >> i & 1]
        r = frank2(f, rows)
        need[mask] = math.log2(r) if r > 0 else 0.0
    return need


def passes_primal(top, need):
    legmap, edges = top
    V = 1 + max(legmap + [v for e in edges for v in e])
    for vs in range(2 ** V):
        side = [(vs >> v) & 1 for v in range(V)]
        inner = sum(1 for u, v in edges if side[u] != side[v])
        for lm in range(16):
            cross = inner + sum(1 for i in range(4) if ((lm >> i) & 1) != side[legmap[i]])
            # legs with bit 0 in lm are on side 0
            mask = sum(1 << i for i in range(4) if not (lm >> i) & 1)
            if need[mask] > cross + 1e-9:
                return False
    return True


def passes_dual(top, need):
    legmap, edges = top
    V = 1 + max(legmap + [v for e in edges for v in e])
    E = len(edges)
    for es in range(2 ** E):
        for lm in range(16):
            sides = {v: set() for v in range(V)}
            for i in range(4):
                sides[legmap[i]].add((lm >> i) & 1)
            for k, (u, v) in enumerate(edges):
                s = (es >> k) & 1
                sides[u].add(s)
                sides[v].add(s)
            split = sum(1 for v in range(V) if len(sides[v]) == 2)
            mask = sum(1 << i for i in range(4) if not (lm >> i) & 1)
            if need[mask] > split + 1e-9:
                return False
    return True


# ------------------------------------------------------------------ SAT for tables
def realizable(top, f, tmpdir):
    legmap, edges = top
    V = 1 + max(legmap + [v for e in edges for v in e])
    E = len(edges)
    # local leg order per vertex: legs first (by leg index), then edges (by edge index)
    inc = {v: [] for v in range(V)}
    for i, v in enumerate(legmap):
        inc[v].append(('L', i))
    for k, (u, v) in enumerate(edges):
        inc[u].append(('E', k))
        inc[v].append(('E', k))
    nv = 0
    tvar = {}
    for v in range(V):
        for a in itertools.product((0, 1), repeat=len(inc[v])):
            nv += 1
            tvar[(v, a)] = nv
    clauses = []
    for x in itertools.product((0, 1), repeat=4):
        terms = []
        for z in itertools.product((0, 1), repeat=E):
            lits = []
            for v in range(V):
                a = tuple(x[i] if kind == 'L' else z[i] for kind, i in inc[v])
                lits.append(tvar[(v, a)])
            nv += 1
            y = nv
            for l in lits:
                clauses.append([-y, l])
            clauses.append([y] + [-l for l in lits])
            terms.append(y)
        # xor chain
        acc = terms[0]
        for t in terms[1:]:
            nv += 1
            s = nv
            clauses += [[-s, acc, t], [-s, -acc, -t], [s, -acc, t], [s, acc, -t]]
            acc = s
        clauses.append([acc] if f[x] else [-acc])
    path = os.path.join(tmpdir, "q.cnf")
    with open(path, "w") as fh:
        fh.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses:
            fh.write(" ".join(map(str, c)) + " 0\n")
    r = subprocess.run([CADICAL, "-q", path], capture_output=True, text=True, timeout=120)
    if r.returncode == 10:
        return True
    if r.returncode == 20:
        return False
    raise RuntimeError("cadical: " + r.stdout[-200:] + r.stderr[-200:])


def d2(Vmax):
    print(f"D2: exact F_2-networks with 4 legs, all topologies with V <= {Vmax} vertices")
    tops = {V: topologies(V) for V in range(1, Vmax + 1)}
    for V in tops:
        print(f"  V={V}: topologies={len(tops[V])}")
    rnd = {x: random.randint(0, 1) for x in itertools.product((0, 1), repeat=4)}
    targets = {
        "distinct 2-bit words [x1x2 != x3x4]": lambda x: int((x[0], x[1]) != (x[2], x[3])),
        "equal 2-bit words (two wires)": lambda x: int((x[0], x[1]) == (x[2], x[3])),
        "xor of words = 11": lambda x: int((x[0] ^ x[2], x[1] ^ x[3]) == (1, 1)),
        "parity of 4 bits": lambda x: x[0] ^ x[1] ^ x[2] ^ x[3],
        "AND of 4 bits": lambda x: int(all(x)),
        "random (seed 7)": lambda x: rnd[x],
    }
    # exhaustive scan of all 65536 functions: the largest value of the minimum pairing rank
    xs = list(itertools.product((0, 1), repeat=4))
    best = (-1, None)
    hist = {}
    for code in range(2 ** 16):
        g = {x: (code >> k) & 1 for k, x in enumerate(xs)}
        mn = min(frank2(g, rows) for rows in ([0, 1], [0, 2], [0, 3]))
        hist[mn] = hist.get(mn, 0) + 1
        if mn > best[0]:
            best = (mn, g)
    print(f"  all 65536 functions on 4 legs: histogram of min pairing rank over F_2 = {dict(sorted(hist.items()))}")
    targets[f"first function with min pairing rank {best[0]}"] = (lambda gg: (lambda x: gg[x]))(best[1])
    with tempfile.TemporaryDirectory() as tmpdir:
        for name, fn in targets.items():
            f = {x: fn(x) for x in itertools.product((0, 1), repeat=4)}
            need = need_table(f)
            lbp = lbd = vstar = None
            for V in range(1, Vmax + 1):
                for top in tops[V]:
                    if lbp is None and passes_primal(top, need):
                        lbp = V
                    if lbd is None and passes_dual(top, need):
                        lbd = V
                    if vstar is None and realizable(top, f, tmpdir):
                        vstar = V
                        vtop = top
                if vstar is not None and lbp is not None and lbd is not None:
                    break
            pr = [int(2 ** need[m]) for m in (0b0011, 0b0101, 0b1001)]
            print(f"  {name}: pairing ranks={pr}  LB_primal={lbp}  LB_dual={lbd}  V*={vstar if vstar else '>' + str(Vmax)}"
                  f"  sound={(vstar is None) or (lbp <= vstar and lbd <= vstar)}"
                  + (f"  witness topology legs->{vtop[0]} edges={vtop[1]}" if vstar else ""))


if __name__ == "__main__":
    Vmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    d1()
    d2(Vmax)
