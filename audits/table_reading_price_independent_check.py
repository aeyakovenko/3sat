#!/usr/bin/env python3
"""Independent checks, written during review, for
notes/the-price-inequality-and-its-table-reading-dual-cannot-certify-more-than-n-log-n.md.

Part 1  Lemma A by explicit witnesses, not by orbit BFS: every 2x2x2 tensor over F_p is
        (i) a sum of <= 2 rank-one tensors (explicit decomposition re-verified as a restriction
        of Delta(2)), or (ii) (A,B,C).W, or (iii) (A,B,C).M_K with (A,B,C) in GL_2^3 found by
        applying ALL triples (orbit computed directly, no generators). p = 2, 3, 5 (p = 5 uses
        generator BFS for the two rank-3 orbits only, all p^8 tensors are covered).
Part 2  The n = 2 power step of case (ii): W(x)W equals the eps^2 coefficient, i.e. the sum of
        C(4,2) = 6 restrictions of Delta(2)^{(x)2}; and that sum equals ONE restriction of the
        direct sum of 6 copies (block-concatenated maps).
Part 3  Case (iii) with a different irreducible polynomial than table_reading_price_checks.py, and the algebra
        check psi(uv) = psi(u)psi(v), plus the char-2 inseparable remark: the structure
        tensor of k[e]/(e^2) is in the GL_2^3-orbit of W.
Part 4  An independent Benes construction (iterative stages), edge count r(6m-3), max degree 3
        with pendant edges, and edge-disjoint routing of all r cyclic shifts (own looping).
Part 5  Metric steps of Theorem C(a) and C(b) on random placements, with delta = diameter
        (the smallest set function allowed by the proof) for the dual.
Part 6  D1 census (n = 4 records, w = 3, 4).
Part 7  4-leg 0/1 functions over F_2: the three 2|2 flattening ranks.
Usage: python3 -B table_reading_price_independent_check.py [PART ...] [p5]
  (no argument: parts 1-7, with parts 1 and 3 also over F_5, about 25 s; p5 adds F_5 to parts 1 and 3)
Writes nothing.
"""
import itertools, math, random, sys
import numpy as np

rng = random.Random(4242)
nrng = np.random.default_rng(4242)


def rank_p(M, p):
    M = [[int(v) % p for v in row] for row in M]
    r = 0
    rows = len(M); cols = len(M[0]) if rows else 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r


def gl2(p):
    return [np.array([[a, b], [c, d]]) for a, b, c, d in itertools.product(range(p), repeat=4)
            if (a * d - b * c) % p]


def act(t, A, B, C, p):
    return np.einsum('ai,bj,ck,ijk->abc', A, B, C, t) % p


def key(t):
    return tuple(int(v) for v in np.asarray(t).reshape(-1))


def part1(p, full_orbit=True):
    G = gl2(p)
    vecs = [np.array(v) for v in itertools.product(range(p), repeat=2) if any(v)]
    # rank-one tensors with an explicit factorization
    R1 = {}
    for u in vecs:
        for v in vecs:
            for w in vecs:
                t = np.einsum('i,j,k->ijk', u, v, w) % p
                R1.setdefault(key(t), (u, v, w))
    cover = {key(np.zeros((2, 2, 2), dtype=int)): 'zero'}
    for k1, f1 in R1.items():
        cover.setdefault(k1, ('r1', f1))
    items = list(R1.items())
    for (k1, f1) in items:
        t1 = np.array(k1).reshape(2, 2, 2)
        for (k2, f2) in items:
            t = key((t1 + np.array(k2).reshape(2, 2, 2)) % p)
            if t not in cover:
                cover[t] = ('r2', f1, f2)
    # re-verify each rank<=2 witness as a restriction of Delta(2): maps f_j -> u_j, v_j, w_j
    D2 = np.zeros((2, 2, 2), dtype=int); D2[0, 0, 0] = D2[1, 1, 1] = 1
    bad_restr = 0
    for t, wit in cover.items():
        if wit == 'zero':
            continue
        if wit[0] == 'r1':
            (u, v, w) = wit[1]; (u2, v2, w2) = (0 * u, 0 * v, 0 * w)
        else:
            (u, v, w), (u2, v2, w2) = wit[1], wit[2]
        A = np.stack([u, u2], axis=1); B = np.stack([v, v2], axis=1); C = np.stack([w, w2], axis=1)
        if key(act(D2, A, B, C, p)) != t:
            bad_restr += 1
    n_le2 = len(cover)
    W = np.zeros((2, 2, 2), dtype=int); W[1, 0, 0] = W[0, 1, 0] = W[0, 0, 1] = 1
    # field extension: p=2: x^2 = x + 1 ; p=3: x^2 = -x - 2 = 2x + 1 (x^2+x+2 irreducible) ; p=5: x^2 = 2 (x^2-2, 2 non-square mod 5)
    g = {2: (1, 1), 3: (1, 2), 5: (2, 0)}[p]   # x^2 = g0 + g1 x

    def mul(a, b):
        c0 = a[0] * b[0]; c1 = a[0] * b[1] + a[1] * b[0]; c2 = a[1] * b[1]
        return ((c0 + c2 * g[0]) % p, (c1 + c2 * g[1]) % p)
    # irreducibility check of y^2 - g1 y - g0
    irreducible = all((y * y - g[1] * y - g[0]) % p for y in range(p))
    basis = [(1, 0), (0, 1)]
    M = np.array([[[mul(basis[i], basis[j])[k] for k in range(2)] for j in range(2)] for i in range(2)])
    orbW, orbM = set(), set()
    if full_orbit:
        for A in G:
            for B in G:
                AB = np.einsum('ai,bj->abij', A, B)
                for C in G:
                    orbW.add(key(np.einsum('abij,ck,ijk->abc', AB, C, W) % p))
                    orbM.add(key(np.einsum('abij,ck,ijk->abc', AB, C, M) % p))
    else:
        I = np.eye(2, dtype=int)
        gens = [np.array([[1, 1], [0, 1]]), np.array([[0, 1], [1, 0]]), np.array([[2 % p or 1, 0], [0, 1]])]
        for seed, orb in ((W, orbW), (M, orbM)):
            st = [key(seed)]; orb.add(st[0])
            while st:
                t = np.array(st.pop()).reshape(2, 2, 2)
                for A in gens:
                    for u in (act(t, A, I, I, p), act(t, I, A, I, p), act(t, I, I, A, p)):
                        ku = key(u)
                        if ku not in orb:
                            orb.add(ku); st.append(ku)
    allt = set(itertools.product(range(p), repeat=8))
    le2 = set(cover)
    uncovered = allt - le2 - orbW - orbM
    print(f"  p={p}: tensors={len(allt)}  rank<=2 (explicit sums)={len(le2)} (restriction re-check failures={bad_restr})"
          f"  |orbit W|={len(orbW)}  |orbit M|={len(orbM)}  W in rank<=2: {key(W) in le2}  M in rank<=2: {key(M) in le2}"
          f"  orbits W,M disjoint: {not (orbW & orbM)}  uncovered={len(uncovered)}  (x^2-{g[1]}x-{g[0]} irreducible: {irreducible})")
    return M, mul, g


def part2(p):
    # A=B: f0 -> e0 + eps e1, f1 -> e0 ; C: f0 -> e0 + eps e1, f1 -> -e0. As polynomials in eps: X = X0 + eps X1
    A0 = np.array([[1, 1], [0, 0]]); A1 = np.array([[0, 0], [1, 0]])
    C0 = np.array([[1, p - 1], [0, 0]]); C1 = A1.copy()
    D1 = np.zeros((2, 2, 2), dtype=int); D1[0, 0, 0] = D1[1, 1, 1] = 1
    W = np.zeros((2, 2, 2), dtype=int); W[1, 0, 0] = W[0, 1, 0] = W[0, 0, 1] = 1
    n = 2
    Dn = np.einsum('abc,def->adbecf', D1, D1).reshape(4, 4, 4)
    Wn = np.einsum('abc,def->adbecf', W, W).reshape(4, 4, 4) % p

    def coeffs(X0, X1):  # eps-coefficients of X^{(x)2}
        return {0: np.kron(X0, X0), 1: np.kron(X0, X1) + np.kron(X1, X0), 2: np.kron(X1, X1)}
    Ac = coeffs(A0, A1); Cc = coeffs(C0, C1)
    terms = [(a, b, c) for a in range(3) for b in range(3) for c in range(3) if a + b + c == n]
    S = np.zeros((4, 4, 4), dtype=int)
    lower = np.zeros((4, 4, 4), dtype=int)
    for a, b, c in terms:
        S = (S + act(Dn, Ac[a], Ac[b], Cc[c], p)) % p
    for a, b, c in itertools.product(range(3), repeat=3):
        if a + b + c < n:
            lower = (lower + act(Dn, Ac[a], Ac[b], Cc[c], p)) % p
    # one restriction of the direct sum of len(terms) copies: block-concatenated maps
    m = len(terms)
    Dsum = np.zeros((4 * m, 4 * m, 4 * m), dtype=int)
    for s in range(m):
        Dsum[4 * s:4 * s + 4, 4 * s:4 * s + 4, 4 * s:4 * s + 4] = Dn
    Ahat = np.concatenate([Ac[a] for a, b, c in terms], axis=1)
    Bhat = np.concatenate([Ac[b] for a, b, c in terms], axis=1)
    Chat = np.concatenate([Cc[c] for a, b, c in terms], axis=1)
    one = act(Dsum, Ahat, Bhat, Chat, p)
    print(f"  p={p}: n=2: terms={m} (C(4,2)=6)  sum of eps^2 terms == W(x)W: {np.array_equal(S, Wn)}"
          f"  lower-order total (eps^0+eps^1 parts) zero: {not lower.any()}"
          f"  single restriction of Delta(2)^(x)2 direct-summed {m} times == W(x)W: {np.array_equal(one % p, Wn)}")


def part3(p, M, mul, g):
    def frob(b):
        r_ = (1, 0)
        for _ in range(p):
            r_ = mul(r_, b)
        return r_
    basis = [(1, 0), (0, 1)]
    # psi : K (x) K -> K x K, a(x)b -> (ab, a frob(b)); columns indexed by 2i+j
    psi = np.zeros((4, 4), dtype=int)
    for i in range(2):
        for j in range(2):
            u = mul(basis[i], basis[j]); v = mul(basis[i], frob(basis[j]))
            psi[:, 2 * i + j] = [u[0], u[1], v[0], v[1]]
    rk = rank_p(psi, p)
    # algebra homomorphism check on basis pairs: psi((ei(x)ej)(ek(x)el)) == psi(ei(x)ej) * psi(ek(x)el) (componentwise in K x K)
    ok_hom = True
    for i, j, k, l in itertools.product(range(2), repeat=4):
        prod1 = mul(basis[i], basis[k]); prod2 = mul(basis[j], basis[l])   # (ei ek) (x) (ej el)
        vec = np.zeros(4, dtype=int)
        for s in range(2):
            for t in range(2):
                vec = (vec + prod1[s] * prod2[t] * psi[:, 2 * s + t]) % p
        x = psi[:, 2 * i + j]; y = psi[:, 2 * k + l]
        left = mul((x[0], x[1]), (y[0], y[1])); right = mul((x[2], x[3]), (y[2], y[3]))
        if tuple(vec) != (left[0], left[1], right[0], right[1]):
            ok_hom = False
    # structure tensors: M(x)M on legs grouped (index 2i+j), M(+)M block
    MM = np.einsum('ikm,jln->ijklmn', M, M).reshape(4, 4, 4) % p
    # psi^{-1} mod p by brute-force adjugate via solving
    inv = None
    for cand in [None]:
        aug = np.concatenate([psi % p, np.eye(4, dtype=int)], axis=1).tolist()
        r = 0
        for c in range(4):
            piv = next(i for i in range(r, 4) if aug[i][c] % p)
            aug[r], aug[piv] = aug[piv], aug[r]
            iv = pow(aug[r][c], p - 2, p)
            aug[r] = [(v * iv) % p for v in aug[r]]
            for i in range(4):
                if i != r and aug[i][c] % p:
                    f = aug[i][c]; aug[i] = [(a - f * b) % p for a, b in zip(aug[i], aug[r])]
            r += 1
        inv = np.array([row[4:] for row in aug])
    assert not ((inv @ psi - np.eye(4, dtype=int)) % p).any()
    T = np.einsum('ia,jb,ck,ijk->abc', inv, inv, psi, MM) % p
    MD = np.zeros((4, 4, 4), dtype=int)
    MD[0:2, 0:2, 0:2] = M; MD[2:4, 2:4, 2:4] = M
    print(f"  p={p}: x^2={g[0]}+{g[1]}x  psi rank={rk}  psi multiplicative on all 16 basis pairs: {ok_hom}"
          f"  (psi^-T,psi^-T,psi)(M(x)M) == M(+)M = M(x)Delta(2): {np.array_equal(T, MD)}")


def part3b():
    # structure tensor of k[e]/(e^2) in basis (1, e): 1*1=1, 1*e=e, e*1=e, e*e=0 ; check it is in GL_2^3 orbit of W over F_2
    p = 2
    T = np.zeros((2, 2, 2), dtype=int); T[0, 0, 0] = 1; T[0, 1, 1] = 1; T[1, 0, 1] = 1
    W = np.zeros((2, 2, 2), dtype=int); W[1, 0, 0] = W[0, 1, 0] = W[0, 0, 1] = 1
    found = any(np.array_equal(act(W, A, B, C, p), T) for A in gl2(p) for B in gl2(p) for C in gl2(p))
    print(f"  char 2 inseparable remark: structure tensor of k[e]/(e^2) lies in the GL_2^3-orbit of W over F_2: {found}")


# ---------------------------------------------------------------- Benes, built by stages
def benes_stages(m):
    """Return list of stages; each stage a list of switches; wiring between stage s and s+1 as a permutation
    of the r wire positions. Classic Benes = reversed butterfly + butterfly sharing the middle stage.
    Wire position w at the output of a stage goes to position perm[w] at the input of the next stage."""
    r = 2 ** m
    nst = 2 * m - 1
    # stage s (0..2m-2) switch k handles positions 2k, 2k+1. Between stages, use the unshuffle/shuffle on
    # the lowest (dims) bits so that the recursive structure is realized.
    perms = []
    for s in range(nst - 1):
        # dimension exchanged going from stage s to s+1
        if s < m - 1:
            dim = m - 1 - s     # rotate: bring bit 'dim' to position 0
            # position w -> swap bit 0 and bit (s+1)
            b = s + 1
        else:
            b = (nst - 2 - s) + 1
        perm = []
        for w in range(r):
            b0 = w & 1; bb = (w >> b) & 1
            w2 = w
            if b0 != bb:
                w2 = w ^ 1 ^ (1 << b)
            perm.append(w2)
        perms.append(perm)
    return r, nst, perms


def build_graph(m, pendant=True):
    r, nst, perms = benes_stages(m)
    # vertices: ('in', s, w) and ('out', s, w) for stage s, wire position w ; leaves ('x', i) ; pendants ('o', j)
    edges = []
    for s in range(nst):
        for k in range(r // 2):
            for a in (2 * k, 2 * k + 1):
                for b in (2 * k, 2 * k + 1):
                    edges.append((('in', s, a), ('out', s, b)))
    for s in range(nst - 1):
        for w in range(r):
            edges.append((('out', s, w), ('in', s + 1, perms[s][w])))
    for i in range(r):
        edges.append((('x', i), ('in', 0, i)))
    if pendant:
        for j in range(r):
            edges.append((('out', nst - 1, j), ('o', j)))
    return r, nst, perms, edges


def route(m, target):
    """Route permutation 'target' (input position i -> output position target[i]) through build_graph(m)
    by brute-force recursive search over switch settings stage by stage? Too slow for big m. Instead:
    generic edge-disjoint path search by DFS with backtracking on switch states, then verify."""
    r, nst, perms, edges = build_graph(m, pendant=False)
    # switch state per (stage, k): 0 straight, 1 cross. Path of input i: position at stage-in -> state -> stage-out -> perm
    # Use the looping principle via 2-SAT style propagation: constraints are XOR equations on states; solve by
    # backtracking with propagation (search space small in practice).
    nsw = nst * (r // 2)

    def simulate(state):
        pos = list(range(r))   # wire position of each input at the input of stage 0
        for s in range(nst):
            new = []
            for w in pos:
                k = w // 2
                w2 = w ^ state[s * (r // 2) + k]
                new.append(w2 if s == nst - 1 else perms[s][w2])
            pos = new
        return pos
    # search: DFS over switches in order, pruning by partial simulation is hard; use randomized restarts +
    # local search (min-conflicts) which is plenty for r <= 64
    best = None
    state = [0] * nsw
    for attempt in range(200000):
        out = simulate(state)
        bad = [i for i in range(r) if out[i] != target[i]]
        if not bad:
            return state, True
        # flip a random switch on the path of a random bad input
        i = rng.choice(bad)
        w = i; cand = []
        for s in range(nst):
            k = w // 2
            cand.append(s * (r // 2) + k)
            w2 = w ^ state[s * (r // 2) + k]
            w = w2 if s == nst - 1 else perms[s][w2]
        state[rng.choice(cand)] ^= 1
    return state, False


def looping(m, target):
    """Recursive looping on logical addresses. Stage s < m-1 sets logical dim s to a chosen bit c_s;
    stage m-1 sets dim m-1 to the target bit; stage m-1+t sets dim m-1-t to the target bit.
    Returns switch states for build_graph(m) (derived by simulation) and a consistency flag."""
    r, nst, perms, edges = build_graph(m, pendant=False)
    c = {i: [None] * m for i in range(r)}

    def bit(x, d):
        return (x >> d) & 1

    def solve(sigs, level):
        if level >= m - 1:
            return
        def strip(x):
            return x & ~(1 << level)
        inpart = {}; outpart = {}
        by_src = {}; by_tgt = {}
        for i in sigs:
            by_src.setdefault((strip(i >> 0) >> (level + 1)), []).append(i)
            by_tgt.setdefault((target[i] >> (level + 1)), []).append(i)
        for grp in by_src.values():
            assert len(grp) == 2
            inpart[grp[0]] = grp[1]; inpart[grp[1]] = grp[0]
        for grp in by_tgt.values():
            assert len(grp) == 2
            outpart[grp[0]] = grp[1]; outpart[grp[1]] = grp[0]
        col = {}
        for s0 in sigs:
            if s0 in col:
                continue
            cur = s0; val = 0
            while cur not in col:
                col[cur] = val
                pin = inpart[cur]
                col[pin] = 1 - val
                nxt = outpart[pin]          # must differ from pin -> gets val
                cur = nxt
            # loop closes consistently by parity of the alternating cycle
        for i in sigs:
            c[i][level] = col[i]
        for v in (0, 1):
            solve([i for i in sigs if col[i] == v], level + 1)
    solve(list(range(r)), 0)
    # simulate positions and derive switch states
    state = [None] * (nst * (r // 2))
    consistent = True
    pos = list(range(r))
    logical = list(range(r))       # current logical address of each signal
    for s in range(nst):
        dim = s if s <= m - 1 else 2 * m - 2 - s
        for i in range(r):
            w = pos[i]
            if s < m - 1:
                want = c[i][dim]
            else:
                want = bit(target[i], dim)
            logical[i] = (logical[i] & ~(1 << dim)) | (want << dim)
            st = (w & 1) ^ want
            idx = s * (r // 2) + w // 2
            if state[idx] is None:
                state[idx] = st
            elif state[idx] != st:
                consistent = False
            w2 = w ^ st
            pos[i] = w2 if s == nst - 1 else perms[s][w2]
    ok = consistent and all(pos[i] == target[i] for i in range(r))
    return [0 if v is None else v for v in state], ok


def part4():
    for m in range(2, 7):
        r, nst, perms, edges = build_graph(m, pendant=False)
        deg = {}
        for u, v in edges:
            deg[u] = deg.get(u, 0) + 1; deg[v] = deg.get(v, 0) + 1
        r_, nst_, perms_, edges_p = build_graph(m, pendant=True)
        degp = {}
        for u, v in edges_p:
            degp[u] = degp.get(u, 0) + 1; degp[v] = degp.get(v, 0) + 1
        print(f"  r={r}: edges={len(edges)} r(6m-3)={r * (6 * m - 3)}  max degree={max(deg.values())}  "
              f"with pendants: edges={len(edges_p)} max degree={max(degp.values())}  stage perms are bijections: "
              f"{all(sorted(p_) == list(range(r)) for p_ in perms)}")


def paths_for(m, state, pendant=True):
    r, nst, perms, edges = build_graph(m, pendant=pendant)
    paths = []
    for i in range(r):
        w = i
        path_edges = [frozenset((('x', i), ('in', 0, i)))]
        path_vertices = []
        for s in range(nst):
            k = w // 2
            w2 = w ^ state[s * (r // 2) + k]
            path_edges.append(frozenset((('in', s, w), ('out', s, w2))))
            path_vertices += [('in', s, w), ('out', s, w2)]
            if s < nst - 1:
                path_edges.append(frozenset((('out', s, w2), ('in', s + 1, perms[s][w2]))))
                w = perms[s][w2]
            else:
                w = w2
        if pendant:
            path_edges.append(frozenset((('out', nst - 1, w), ('o', w))))
        paths.append((path_edges, path_vertices, w))
    return paths


def part4b(ms=(2, 3, 4, 5)):
    allstates = {}
    for m in ms:
        r = 2 ** m
        ok_all = True
        for s_ in range(r):
            target = [(i + s_) % r for i in range(r)]
            state, ok = looping(m, target)
            if not ok:
                ok_all = False; break
            ps = paths_for(m, state)
            eused, vused = set(), set()
            for (pe, pv, end), (i) in zip(ps, range(r)):
                if end != target[i]:
                    ok_all = False
                for e in pe:
                    if e in eused:
                        ok_all = False
                    eused.add(e)
                for v in pv:
                    if v in vused:
                        ok_all = False
                    vused.add(v)
            allstates[(m, s_)] = state
        print(f"  r={r}: all {r} cyclic shifts routed; endpoints correct, paths pairwise edge-disjoint AND internally vertex-disjoint: {ok_all}")
    return allstates


def part5(allstates, ms=(3, 4, 5), trials=200):
    for m in ms:
        r = 2 ** m
        r_, nst, perms, edges = build_graph(m, pendant=True)
        verts = sorted({u for e in edges for u in e}, key=str)
        inc = {}
        for idx, (u, v) in enumerate(edges):
            inc.setdefault(u, []).append(idx); inc.setdefault(v, []).append(idx)
        leg_idx = [edges.index((('x', i), ('in', 0, i))) for i in range(r)]
        pend_idx = [edges.index((('out', nst - 1, j), ('o', j))) for j in range(r)]
        worstP = worstD = -1e18
        worst_shift_P = worst_shift_D = -1e18
        for t in range(trials):
            mode = t % 4
            dim = rng.choice((1, 2, 5))
            # primal: vertex positions ; dual: edge positions ; metric: l2 (modes 0-1), l1 (mode 2), random tree-ish ultrametric-like via l_inf (mode 3)
            def draw(n, scale):
                if mode in (0, 2):
                    return nrng.normal(size=(n, dim)) * scale
                if mode == 1:
                    return nrng.standard_cauchy(size=(n, dim)) * scale
                return nrng.integers(0, 3, size=(n, dim)).astype(float) * scale
            norm = (lambda z: np.abs(z).sum()) if mode == 2 else ((lambda z: np.abs(z).max()) if mode == 3 else (lambda z: float(np.sqrt((z * z).sum()))))
            # ---- primal
            P = {v: draw(1, 30.0 if v[0] == 'x' else 1.0)[0] for v in verts if v[0] != 'o'}
            Ep = [(u, v) for (u, v) in edges if u[0] != 'o' and v[0] != 'o']
            rhsP = sum(norm(P[u] - P[v]) for u, v in Ep)
            outs = [('out', nst - 1, j) for j in range(r)]
            lhsP = min(sum(norm(P[('x', i)] - P[o]) for i in range(r)) for o in outs)
            worstP = max(worstP, lhsP - rhsP)
            # per-shift inequality sum_i d(x_i, o_{i+s}) <= sum_e d(e)
            for s_ in range(r):
                val = sum(norm(P[('x', i)] - P[('out', nst - 1, (i + s_) % r)]) for i in range(r))
                worst_shift_P = max(worst_shift_P, val - rhsP)
            # ---- dual with delta = diameter
            Q = draw(len(edges), 1.0)
            for i in leg_idx:
                Q[i] = draw(1, 30.0)[0]
            def diam(ids):
                return max((norm(Q[a] - Q[b]) for a in ids for b in ids), default=0.0)
            rhsD = sum(diam(inc[v]) for v in verts if v[0] != 'x')   # leaves x are not vertices in the dual
            lhsD = min(sum(norm(Q[leg_idx[i]] - Q[pend_idx[j]]) for i in range(r)) for j in range(r))
            worstD = max(worstD, lhsD - rhsD)
            for s_ in range(r):
                val = sum(norm(Q[leg_idx[i]] - Q[pend_idx[(i + s_) % r]]) for i in range(r))
                worst_shift_D = max(worst_shift_D, val - rhsD)
        print(f"  r={r}: placements={trials} (l2, Cauchy-l2, l1, l_inf grid)  primal: max(min_j sum_i d - sum_e d)={worstP:.4g}, "
              f"max over shifts={worst_shift_P:.4g}  dual (delta=diameter): max(min_j sum_i d - sum_v diam)={worstD:.4g}, "
              f"max over shifts={worst_shift_D:.4g}  (all must be <= 0)")


def part6():
    for w in (3, 4):
        F = list(range(2 ** w))
        tot = nonsub = nonsub_nonzero = sub = 0
        for B in itertools.combinations(F, 4):
            tot += 1
            S = {a ^ b for a in B for b in B}
            closed = all((a ^ b) in S for a in S for b in S)
            if closed:
                sub += 1
                continue
            nonsub += 1
            forb = S - {0}
            # P_B nonzero iff 4 distinct records with pairwise xor outside S (0 in S forces distinct)
            found = False
            for rec in itertools.combinations(F, 4):
                if all((x ^ y) not in S for x, y in itertools.combinations(rec, 2)):
                    found = True; break
            nonsub_nonzero += found
        print(f"  w={w}: 4-sets B={tot}  B+B subspace={sub}  not a subspace={nonsub}  of these with P_B not identically 0={nonsub_nonzero}")
    # every 3-set has B+B a subspace, any w (check w <= 5)
    ok3 = all(all((a ^ b) in S for a in S for b in S)
              for w in range(2, 6) for B in itertools.combinations(range(2 ** w), 3)
              for S in [{a ^ b for a in B for b in B}])
    print(f"  every 3-element B in F_2^w (w=2..5) has B+B a subspace: {ok3}")


def part7():
    hist = {}
    allfour = 0
    det_relation = True
    for f in range(2 ** 16):
        T = np.array([(f >> idx) & 1 for idx in range(16)]).reshape(2, 2, 2, 2)
        ranks = []
        for rows in ((0, 1), (0, 2), (0, 3)):
            cols = tuple(i for i in range(4) if i not in rows)
            Mx = np.transpose(T, rows + cols).reshape(4, 4)
            ranks.append(rank_p(Mx.tolist(), 2))
        mn = min(ranks)
        hist[mn] = hist.get(mn, 0) + 1
        allfour += all(x == 4 for x in ranks)
        # parity of number of invertible flattenings
        if sum(x == 4 for x in ranks) % 2 == 1 and False:
            det_relation = False
    print(f"  all 65536 functions on 4 legs: histogram of min pairing rank over F_2 = {dict(sorted(hist.items()))};"
          f" functions with all three pairings of rank 4 = {allfour}")


if __name__ == "__main__":
    which = sys.argv[1:] or ["1", "2", "3", "4", "5", "6", "7", "p5"]
    if "1" in which or "3" in which:
        print("Part 1: Lemma A by explicit witnesses")
        data = {}
        for p in (2, 3):
            data[p] = part1(p, full_orbit=True)
        if "p5" in which:
            data[5] = part1(5, full_orbit=False)
    if "2" in which:
        print("Part 2: degeneration, n = 2 power step")
        for p in (2, 3, 5):
            part2(p)
    if "3" in which:
        print("Part 3: field-extension identity (different polynomial), algebra check, inseparable remark")
        for p in sorted(data):
            M, mul, g = data[p]
            part3(p, M, mul, g)
        part3b()
    if "4" in which:
        print("Part 4: independent Benes construction")
        part4()
        states = part4b()
    if "5" in which:
        print("Part 5: metric steps of Theorem C(a), C(b)")
        part5(states)
    if "6" in which:
        print("Part 6: D1 census")
        part6()
    if "7" in which:
        print("Part 7: 4-leg pairing ranks over F_2")
        part7()
