#!/usr/bin/env python3
"""Finite checks for notes/the-price-inequality-and-its-table-reading-dual-cannot-certify-more-than-n-log-n.md:
table-reading price inequalities.

Check A  every 2x2x2 table over F_p (p = 2, 3) is spectrally dominated by the unit tensor
         Delta(2) on its three legs: GL_2(F_p)^3 orbits, ranks, and the three cases
         (rank <= 2: restriction; W orbit: degree-1 degeneration identity over F_p[eps];
          field-extension orbit M: algebra identity M (x) M  ~=  M (x) Delta(2)).
Check B  the cap graph G_r (Benes network of K_{2,2} switch gadgets, legs at the inputs):
         trivalence; every permutation is routed by edge-disjoint input->output paths
         (looping algorithm, all permutations at r = 4, 8; samples at r = 16, 32);
         the cut-rank instance of the cap (min edge cut and min vertex cut between any
         two complementary leg sets >= min(|A|, |A^c|)), exhaustive over leg subsets;
         the metric inequality min_j sum_i d(u_i, v_j) <= sum_e d(e) on random Euclidean
         placements.
Check C  soundness of the primal and dual (table-reading) cut-rank inequalities on random
         small trivalent networks with random tables over F_2 and F_3.
Usage: python3 -B table_reading_price_checks.py [A] [B] [C]   (no argument: all three, about 18 s)
Writes nothing.
"""
import itertools
import math
import random
import sys

import numpy as np

random.seed(20261128)
np.random.seed(20261128)


# ---------------------------------------------------------------- linear algebra mod p
def rank_mod_p(M, p):
    M = [list(map(lambda v: v % p, row)) for row in M]
    rows, cols = len(M), (len(M[0]) if M else 0)
    r = 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c] % p:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c] % p:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
        if r == rows:
            break
    return r


def gl2(p):
    out = []
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a * d - b * c) % p:
            out.append(((a, b), (c, d)))
    return out


def apply3(t, A, B, C, p):
    """t: dict-free 2x2x2 tuple, index 4i+2j+k. returns (A x B x C) t."""
    T = np.array(t, dtype=np.int64).reshape(2, 2, 2)
    T = np.einsum('ai,bj,ck,ijk->abc', np.array(A), np.array(B), np.array(C), T) % p
    return tuple(int(v) for v in T.reshape(-1))


def rank_one_set(p):
    vecs = [v for v in itertools.product(range(p), repeat=2) if any(v)]
    s = set()
    for u in vecs:
        for v in vecs:
            for w in vecs:
                s.add(tuple((u[i] * v[j] * w[k]) % p for i in range(2) for j in range(2) for k in range(2)))
    return s


def add_t(a, b, p):
    return tuple((x + y) % p for x, y in zip(a, b))


def check_a():
    print("Check A: 2x2x2 tables over F_p versus the unit tensor Delta(2)")
    for p in (2, 3):
        G = gl2(p)
        zero = (0,) * 8
        R1 = rank_one_set(p)
        R2 = {add_t(a, b, p) for a in R1 for b in R1} | R1 | {zero}
        R3 = {add_t(a, b, p) for a in R2 for b in R1} | R2
        allt = set(itertools.product(range(p), repeat=8))
        rank = {}
        for t in allt:
            rank[t] = 0 if t == zero else 1 if t in R1 else 2 if t in R2 else 3 if t in R3 else 4
        # W tensor and field-extension tensor M (multiplication in F_p[x]/(g), g irreducible)
        W = tuple(1 if (i, j, k) in ((1, 0, 0), (0, 1, 0), (0, 0, 1)) else 0
                  for i in range(2) for j in range(2) for k in range(2))
        g = {2: (1, 1), 3: (1, 0)}[p]   # x^2 = g0 + g1 x : p=2: x^2=x+1 ; p=3: x^2 = -1 -> (p-1, 0)
        if p == 3:
            g = (2, 0)

        def mul(a, b):  # a, b coefficient pairs (c0 + c1 x)
            c0 = a[0] * b[0]
            c1 = a[0] * b[1] + a[1] * b[0]
            c2 = a[1] * b[1]
            return ((c0 + c2 * g[0]) % p, (c1 + c2 * g[1]) % p)
        basis = [(1, 0), (0, 1)]
        M = tuple(mul(basis[i], basis[j])[k] for i in range(2) for j in range(2) for k in range(2))
        # orbits by BFS with single-leg generators
        seen = {}
        orbits = []
        I2 = ((1, 0), (0, 1))
        for t in sorted(allt):
            if t in seen:
                continue
            idx = len(orbits)
            orb = [t]
            seen[t] = idx
            stack = [t]
            while stack:
                u = stack.pop()
                for A in G:
                    for v in (apply3(u, A, I2, I2, p), apply3(u, I2, A, I2, p), apply3(u, I2, I2, A, p)):
                        if v not in seen:
                            seen[v] = idx
                            orb.append(v)
                            stack.append(v)
            orbits.append(orb)
        summary = []
        bad = 0
        for orb in orbits:
            r = rank[orb[0]]
            ranks = {rank[u] for u in orb}
            kind = None
            if r <= 2:
                kind = "rank<=2 (restriction of Delta(2))"
            elif W in orb:
                kind = "W orbit (degeneration)"
            elif M in orb:
                kind = "field-extension orbit M"
            else:
                kind = "UNCLASSIFIED"
                bad += 1
            summary.append((r, len(orb), kind, len(ranks)))
        print(f"  p={p}: tensors={len(allt)} orbits={len(orbits)} rank histogram="
              f"{dict(sorted(__import__('collections').Counter(rank.values()).items()))}")
        for r, sz, kind, nr in sorted(summary):
            print(f"    orbit rank={r} size={sz} kind={kind} (rank constant on orbit: {nr == 1})")
        print(f"  p={p}: unclassified orbits={bad}")

        # (ii) W degeneration over F_p[eps]: A = C maps f0 -> e0 + eps e1, f1 -> e0 (third leg: f1 -> -e0)
        # tensor coefficients as polynomials in eps, degree <= 3
        def poly_tensor():
            T = [[0] * 4 for _ in range(8)]   # 8 entries, coefficients eps^0..eps^3
            for j in range(2):  # Delta(2) = sum_j f_j f_j f_j
                vecs = []
                for leg in range(3):
                    if j == 0:
                        vecs.append([(1, 0), (0, 1)])   # e0 coeff (1 + 0 eps), e1 coeff (0 + 1 eps)
                    else:
                        s = (p - 1) if leg == 2 else 1
                        vecs.append([(s, 0), (0, 0)])
                for i, jj, k in itertools.product(range(2), repeat=3):
                    a, b, c = vecs[0][i], vecs[1][jj], vecs[2][k]
                    # multiply three linear polys in eps
                    prod = [1]
                    for q in (a, b, c):
                        new = [0] * (len(prod) + 1)
                        for d, coef in enumerate(prod):
                            new[d] += coef * q[0]
                            new[d + 1] += coef * q[1]
                        prod = new
                    for d, coef in enumerate(prod):
                        T[4 * i + 2 * jj + k][d] = (T[4 * i + 2 * jj + k][d] + coef) % p
            return T
        T = poly_tensor()
        c0 = tuple(T[e][0] for e in range(8))
        c1 = tuple(T[e][1] for e in range(8))
        print(f"  p={p}: W degeneration: eps^0 coefficient zero={c0 == zero}  eps^1 coefficient == W: {c1 == W}")

        # (iii) M (x) M  ~=  M (x) Delta(2) via a (x) b -> (ab, a sigma(b)), sigma = Frobenius
        def frob(b):
            r_ = (1, 0)
            for _ in range(p):
                r_ = mul(r_, b)
            return r_
        # psi on basis of K(x)K: (e_i (x) e_j) -> (e_i e_j, e_i sigma(e_j)) in K x K, coordinates 4
        psi = np.zeros((4, 4), dtype=np.int64)
        for i in range(2):
            for j in range(2):
                col = 2 * i + j
                u = mul(basis[i], basis[j])
                v = mul(basis[i], frob(basis[j]))
                psi[:, col] = [u[0], u[1], v[0], v[1]]
        rk = rank_mod_p(psi.tolist(), p)
        # inverse mod p
        def inv_mod(Mx):
            n = len(Mx)
            aug = [list(Mx[i]) + [1 if i == j else 0 for j in range(n)] for i in range(n)]
            for c in range(n):
                piv = next(i for i in range(c, n) if aug[i][c] % p)
                aug[c], aug[piv] = aug[piv], aug[c]
                iv = pow(aug[c][c], p - 2, p)
                aug[c] = [(x * iv) % p for x in aug[c]]
                for i in range(n):
                    if i != c and aug[i][c] % p:
                        f = aug[i][c]
                        aug[i] = [(x - f * y) % p for x, y in zip(aug[i], aug[c])]
            return np.array([row[n:] for row in aug], dtype=np.int64)
        psi_inv = inv_mod(psi.tolist())
        Mt = np.array(M).reshape(2, 2, 2)
        MM = np.einsum('ikm,jln->ijklmn', Mt, Mt).reshape(4, 4, 4) % p   # structure tensor of K (x) K
        # structure tensor transforms: MB[a,b,c] = sum psi_inv[i,a] psi_inv[j,b] psi[c,k] MM[i,j,k]
        MB = np.einsum('ia,jb,ck,ijk->abc', psi_inv, psi_inv, psi, MM) % p
        MD = np.zeros((4, 4, 4), dtype=np.int64)   # M (x) Delta(2): block index shared on all three legs
        for blk in range(2):
            for i, j, k in itertools.product(range(2), repeat=3):
                MD[2 * blk + i, 2 * blk + j, 2 * blk + k] = Mt[i, j, k]
        print(f"  p={p}: psi rank={rk} (4 = invertible); (psi^-T,psi^-T,psi)(M(x)M) == M(x)Delta(2): "
              f"{np.array_equal(MB, MD)}; rank_F{p}(M)={rank[M]}")


# ---------------------------------------------------------------- Benes graph of K22 switches
def benes_switch_list(r):
    """Recursive Benes network. Returns (num_switches, wiring) where switches are numbered and
    'conn' lists edges (switch_out_port -> switch_in_port); in_ports[i] = (switch, port) for input i,
    out_ports[j] = (switch, port) for output j."""
    sw = []          # each switch: id
    conn = []        # ((s, outport), (s2, inport))

    def build(r_):
        if r_ == 2:
            s = len(sw)
            sw.append(s)
            return [(s, 0), (s, 1)], [(s, 0), (s, 1)], {'type': 'leaf', 's': s}
        first = []
        for i in range(r_ // 2):
            s = len(sw)
            sw.append(s)
            first.append(s)
        up_in, up_out, up_tree = build(r_ // 2)
        lo_in, lo_out, lo_tree = build(r_ // 2)
        last = []
        for i in range(r_ // 2):
            s = len(sw)
            sw.append(s)
            last.append(s)
        for i in range(r_ // 2):
            conn.append(((first[i], 0), up_in[i]))
            conn.append(((first[i], 1), lo_in[i]))
            conn.append((up_out[i], (last[i], 0)))
            conn.append((lo_out[i], (last[i], 1)))
        ins = [(first[i // 2], i % 2) for i in range(r_)]
        outs = [(last[j // 2], j % 2) for j in range(r_)]
        return ins, outs, {'type': 'node', 'first': first, 'last': last, 'up': up_tree, 'lo': lo_tree}

    ins, outs, tree = build(r)
    return len(sw), conn, ins, outs, tree


def benes_graph(r):
    """Vertices: leaf x_i (legs), and per switch s: in-vertices (s,'i',0/1), out-vertices (s,'o',0/1).
    Edges: leg edges x_i - (s,'i',port); K22 inside each switch; stage wires (s,'o',a) - (s2,'i',b)."""
    nsw, conn, ins, outs, tree = benes_switch_list(r)
    edges = []
    for s in range(nsw):
        for a in range(2):
            for b in range(2):
                edges.append(((s, 'i', a), (s, 'o', b)))
    for (s, a), (s2, b) in conn:
        edges.append(((s, 'o', a), (s2, 'i', b)))
    legs = [('x', i) for i in range(r)]
    for i, (s, a) in enumerate(ins):
        edges.append((legs[i], (s, 'i', a)))
    outv = [(s, 'o', a) for (s, a) in outs]
    return edges, legs, outv, nsw, conn, ins, outs, tree


def route_benes(r, perm):
    """Looping algorithm. Returns the set of switch states {switch: 0 straight / 1 cross}."""
    nsw, conn, ins, outs, tree = benes_switch_list(r)
    state = {}

    def solve(t, perm_):
        n = len(perm_)
        if t['type'] == 'leaf':
            state[t['s']] = 0 if perm_[0] == 0 else 1
            return
        first, last = t['first'], t['last']
        inv = [0] * n
        for i, j in enumerate(perm_):
            inv[j] = i
        sub = [None] * n   # 0 = upper, 1 = lower, for each input
        for start in range(n):
            if sub[start] is not None:
                continue
            i = start
            side = 0
            while sub[i] is None:
                sub[i] = side
                sub[i ^ 1] = 1 - side
                # partner input i^1 goes on 1-side; its output perm_[i^1]; the output switch partner
                j = perm_[i ^ 1] ^ 1        # other output on the same output switch
                i = inv[j]                  # that output's input must use 'side' again? it must use 1-(1-side)=side
                # output switch: the two outputs on one switch come from different subnetworks
                # perm_[i^1] arrives via side 1-side, so output j must arrive via side -> input inv[j] on side
                side = side
                if sub[i] is not None and sub[i] != side:
                    raise RuntimeError("looping conflict")
        up_perm = [None] * (n // 2)
        lo_perm = [None] * (n // 2)
        for i in range(n):
            j = perm_[i]
            if sub[i] == 0:
                up_perm[i // 2] = j // 2
            else:
                lo_perm[i // 2] = j // 2
        for k in range(n // 2):
            # input switch k: input 2k goes upper -> straight
            state[first[k]] = 0 if sub[2 * k] == 0 else 1
            # output switch k: output 2k comes from upper -> straight
            state[last[k]] = 0 if sub[inv[2 * k]] == 0 else 1
        solve(t['up'], up_perm)
        solve(t['lo'], lo_perm)

    solve(tree, list(perm))
    return state


def paths_from_state(r, state):
    edges, legs, outv, nsw, conn, ins, outs, tree = benes_graph(r)
    nxt = {}
    for (s, a), (s2, b) in conn:
        nxt[(s, 'o', a)] = (s2, 'i', b)
    endset = {v: j for j, v in enumerate(outv)}
    paths = []
    for i in range(r):
        s, a = ins[i]
        v = (s, 'i', a)
        path = [legs[i], v]
        while True:
            s, _, a = v
            b = a ^ state[s]
            w = (s, 'o', b)
            path.append(w)
            if w in endset:
                break
            v = nxt[w]
            path.append(v)
        paths.append((path, endset[w]))
    return paths


def check_b():
    import networkx as nx
    print("Check B: the cap graph G_r (Benes of K22 switches, legs at inputs)")
    for r in (4, 8, 16, 32):
        edges, legs, outv, nsw, conn, ins, outs, tree = benes_graph(r)
        deg = {}
        for u, v in edges:
            deg[u] = deg.get(u, 0) + 1
            deg[v] = deg.get(v, 0) + 1
        V = len(deg)
        perms = list(itertools.permutations(range(r))) if r <= 8 else \
            [tuple(np.random.permutation(r)) for _ in range(2000)]
        bad = 0
        for perm in perms:
            st = route_benes(r, perm)
            ps = paths_from_state(r, st)
            used = set()
            ok = True
            for i, (path, end) in enumerate(ps):
                if end != perm[i]:
                    ok = False
                for e in zip(path, path[1:]):
                    key = frozenset(e)
                    if key in used:
                        ok = False
                    used.add(key)
            bad += (not ok)
        print(f"  r={r}: switches={nsw} vertices={V} edges={len(edges)} max degree={max(deg.values())} "
              f"edges/(r log2 r)={len(edges) / (r * math.log2(r)):.3f} permutations checked={len(perms)} "
              f"failures (wrong endpoint or shared edge)={bad}")
    # cut-rank instance: min edge cut and min vertex cut between complementary leg sets
    for r in (4, 8):
        edges, legs, outv, *_ = benes_graph(r)
        Gx = nx.Graph()
        for u, v in edges:
            Gx.add_edge(u, v)
        worst_e = worst_v = 10 ** 9
        for mask in range(1, 2 ** r - 1):
            A = [legs[i] for i in range(r) if mask >> i & 1]
            B = [legs[i] for i in range(r) if not mask >> i & 1]
            need = min(len(A), len(B))
            H = nx.DiGraph()
            for u, v in edges:
                H.add_edge(u, v, capacity=1)
                H.add_edge(v, u, capacity=1)
            for a in A:
                H.add_edge('S', a, capacity=10 ** 6)
            for b in B:
                H.add_edge(b, 'T', capacity=10 ** 6)
            fe = nx.maximum_flow_value(H, 'S', 'T')
            # vertex version: split every non-leaf vertex with capacity 1 (edges infinite)
            K = nx.DiGraph()
            for v in Gx.nodes:
                if v[0] == 'x':
                    continue
                K.add_edge((v, 'in'), (v, 'out'), capacity=1)

            def node_in(v):
                return v if v[0] == 'x' else (v, 'in')

            def node_out(v):
                return v if v[0] == 'x' else (v, 'out')
            for u, v in edges:
                K.add_edge(node_out(u), node_in(v), capacity=10 ** 6)
                K.add_edge(node_out(v), node_in(u), capacity=10 ** 6)
            for a in A:
                K.add_edge('S', a, capacity=10 ** 6)
            for b in B:
                K.add_edge(b, 'T', capacity=10 ** 6)
            fv = nx.maximum_flow_value(K, 'S', 'T')
            worst_e = min(worst_e, fe - need)
            worst_v = min(worst_v, fv - need)
        print(f"  r={r}: over all {2 ** r - 2} proper leg subsets A: min(edge cut - min(|A|,|A^c|))={worst_e}, "
              f"min(vertex cut - min(|A|,|A^c|))={worst_v}  (both must be >= 0)")
    # metric inequality on random Euclidean placements (Euclidean space is CAT(0))
    for r in (8, 16, 32):
        edges, legs, outv, *_ = benes_graph(r)
        verts = sorted({u for e in edges for u in e}, key=str)
        worst = -1e18
        for trial in range(300):
            dim = random.choice((1, 2, 3, 8))
            mode = trial % 3
            P = {}
            for v in verts:
                if mode == 0:
                    P[v] = np.random.randn(dim)
                elif mode == 1:   # legs spread far apart, the rest near the origin
                    P[v] = np.random.randn(dim) * (50.0 if v[0] == 'x' else 0.1)
                else:             # heavy-tailed
                    P[v] = np.random.standard_cauchy(dim)
            tot = sum(np.linalg.norm(P[u] - P[v]) for u, v in edges)
            best = min(sum(np.linalg.norm(P[x] - P[o]) for x in legs) for o in outv)
            worst = max(worst, best - tot)
        print(f"  r={r}: random Euclidean placements=300  max(min_j sum_i d(x_i,v_j) - sum_e d(e))={worst:.4g} (must be <= 0)")


# ---------------------------------------------------------------- random networks, cut-rank inequalities
def random_network(V, N, p):
    """Random multigraph with V vertices of degree exactly 3 or less; N legs.
    Returns (vertex list of incident edge ids, edge list (u, v) with v = -1 for legs, tables)."""
    while True:
        stubs = [v for v in range(V) for _ in range(3)]
        random.shuffle(stubs)
        legs = stubs[:N]
        rest = stubs[N:]
        if len(rest) % 2:
            rest = rest[:-1]   # one vertex gets degree 2
        edges = [(v, -1) for v in legs]
        ok = True
        for k in range(0, len(rest), 2):
            if rest[k] == rest[k + 1]:
                ok = False
                break
            edges.append((rest[k], rest[k + 1]))
        if ok:
            break
    inc = {v: [] for v in range(V)}
    for eid, (u, v) in enumerate(edges):
        inc[u].append(eid)
        if v >= 0:
            inc[v].append(eid)
    tables = {v: np.random.randint(0, p, size=(2,) * len(inc[v])) for v in range(V)}
    # sometimes use product (rank-one) or GHZ tables to vary
    for v in range(V):
        c = random.random()
        d = len(inc[v])
        if c < 0.15 and d > 0:
            t = np.ones((), dtype=np.int64)
            for _ in range(d):
                t = np.multiply.outer(t, np.random.randint(0, p, size=2))
            tables[v] = t % p
        elif c < 0.3 and d > 0:
            t = np.zeros((2,) * d, dtype=np.int64)
            t[(0,) * d] = 1
            t[(1,) * d] = 1
            tables[v] = t
    return inc, edges, tables


def contract(inc, edges, tables, p, N):
    letters = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
    terms = []
    ops = []
    for v, es in inc.items():
        terms.append(''.join(letters[e] for e in es))
        ops.append(tables[v].astype(np.int64))
    out = ''.join(letters[e] for e in range(N))   # legs are edges 0..N-1
    expr = ','.join(terms) + '->' + out
    T = np.einsum(expr, *ops, optimize='greedy')
    return np.asarray(T) % p


def flat_rank(T, rows, p):
    T = np.asarray(T)
    nd = T.ndim
    cols = [i for i in range(nd) if i not in rows]
    if not rows or not cols:
        return 1 if np.any(T % p) else 0
    M = np.transpose(T, list(rows) + cols).reshape(2 ** len(rows), 2 ** len(cols))
    return rank_mod_p(M.tolist(), p)


def check_c():
    print("Check C: primal (edge-cut) and dual (vertex-table) cut-rank inequalities on random networks")
    for p in (2, 3):
        trials = 0
        viol_primal = viol_dual = 0
        tight_dual_below_primal = 0
        for _ in range(250):
            V = random.randint(3, 7)
            N = random.randint(2, min(6, 3 * V - 2))
            inc, edges, tables = random_network(V, N, p)
            if len(edges) > 20:
                continue
            f = contract(inc, edges, tables, p, N)
            if not np.any(np.asarray(f)):
                continue
            for _ in range(20):
                trials += 1
                # dual: sites are edges; random side per edge
                side = [random.randint(0, 1) for _ in edges]
                rowsL = [i for i in range(N) if side[i] == 0]
                lhs = math.log2(max(1, flat_rank(f, rowsL, p)))
                rhs = 0.0
                for v, es in inc.items():
                    rv = [k for k, e in enumerate(es) if side[e] == 0]
                    rhs += math.log2(max(1, flat_rank(tables[v], rv, p)))
                if lhs > rhs + 1e-9:
                    viol_dual += 1
                # primal: sites are vertices (legs sit at their own leaf); random side per vertex and per leg
                vside = {v: random.randint(0, 1) for v in inc}
                lside = [random.randint(0, 1) for _ in range(N)]
                rowsP = [i for i in range(N) if lside[i] == 0]
                lhsP = math.log2(max(1, flat_rank(f, rowsP, p)))
                cross = 0
                for eid, (u, v) in enumerate(edges):
                    su = vside[u]
                    sv = lside[eid] if v < 0 else vside[v]
                    cross += (su != sv)
                if lhsP > cross + 1e-9:
                    viol_primal += 1
                # dual with all-GHZ tables (topology only): split vertices count 1 each
                ghz = sum(1 for v, es in inc.items() if len({side[e] for e in es}) == 2)
                if rhs < ghz:
                    tight_dual_below_primal += 1
        print(f"  p={p}: (network, cut) trials={trials} dual violations={viol_dual} primal violations={viol_primal} "
              f"cases where actual tables give a smaller dual bound than all-GHZ={tight_dual_below_primal}")


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C"]
    if "A" in which:
        check_a()
    if "B" in which:
        check_b()
    if "C" in which:
        check_c()
