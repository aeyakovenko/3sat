#!/usr/bin/env python3
"""Finite checks for the unique-witness verifier measure U(SAT), for the journal note
unique-witness-verifier-size-of-sat-and-unsat.md.

Part 1  Witness counts of the journal's quadratic exact-network construction
        (notes/exact-network-ceiling-for-ordinary-sat.md), instantiated on all
        model sets of v <= 3 variables, over F_2 (read as a 0/1 network, i.e.
        a nondeterministic circuit whose accepting count is taken mod 2) and
        over F_3 (signed weights).  Shows exactly where counts stop being 0/1.
Part 2  Positive cut-factorisation lemma (the note's cut lemma) on compact
        deterministic computations: random fan-in-2 circuits turned into
        "guess every gate value" verifiers (the template of the RAM-trace
        simulation), random input bipartitions, random placement of every
        auxiliary variable and every constraint.  Checks the identity
        count(x) = sum_sigma alpha_sigma(x_A) beta_sigma(x_B), that the
        accepting rectangles are disjoint, and rank_Q, rank_F2 <= 2^c.
Part 3  The same factorisation on one trial of the quadratic construction at
        the clause-split cut: the identity holds for the count, the F_2 bound
        holds, but rank_Q of the decided parity exceeds 2^c (so no
        unambiguous verifier has a cut that small): the lemma is sensitive
        to uniqueness.
Part 4  The SAT verdict itself at the clause-split cut (disjointness type):
        rank over Q and F_2 coincide, and the full quadratic construction's
        crossing exceeds log2 rank, so the per-cut lemma cannot separate it
        from an unambiguous verifier.

Part 1b builds the tagged F_2 network of Part 1 explicitly (v <= 2) and
        counts its accepting configurations by brute force.
Part 5  Summing the per-cut bound over prefix cuts is false even for a
        linear-size deterministic circuit (inner product mod 2).

Usage: python3 -B unique_witness_verifier_checks.py   (no arguments; about 20 s).  Pure Python + numpy.
The key "full_construction_crossing_at_least_r*v" in Part 4 is the heuristic
r*v (one crossing per trial and variable), not a computed cut.
"""
import itertools
import random
import sys
from fractions import Fraction

import numpy as np

rng = random.Random(20261128)

# ----------------------------------------------------------------- ranks
def rank_f2(rows):
    """rows: list of 0/1 lists.  Rank over F_2 via bitsets."""
    basis = {}
    r = 0
    for row in rows:
        x = 0
        for b in row:
            x = (x << 1) | (b & 1)
        while x:
            h = x.bit_length() - 1
            if h in basis:
                x ^= basis[h]
            else:
                basis[h] = x
                r += 1
                break
    return r


def rank_mod_p(M, p=2147483647):
    """Rank over F_p (p < 2^31) of an integer matrix; a LOWER bound for rank_Q."""
    A = np.array(M, dtype=np.int64) % p
    n, m = A.shape
    r = 0
    for col in range(m):
        piv = None
        for i in range(r, n):
            if A[i, col] != 0:
                piv = i
                break
        if piv is None:
            continue
        A[[r, piv]] = A[[piv, r]]
        inv = pow(int(A[r, col]), p - 2, p)
        A[r] = (A[r] * inv) % p
        colv = A[:, col].copy()
        colv[r] = 0
        nz = np.nonzero(colv)[0]
        if len(nz):
            A[nz] = (A[nz] - (colv[nz, None] * A[r][None, :]) % p) % p
        r += 1
        if r == n:
            break
    return r


def rank_q_exact(M):
    """Exact rank over Q (Fractions); use only for small matrices."""
    A = [[Fraction(v) for v in row] for row in M]
    n = len(A)
    m = len(A[0]) if n else 0
    r = 0
    for col in range(m):
        piv = next((i for i in range(r, n) if A[i][col] != 0), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        pv = A[r][col]
        for i in range(n):
            if i != r and A[i][col] != 0:
                f = A[i][col] / pv
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r

# ------------------------------------------------------- finite fields
def gf_tables(p, d):
    """Find a primitive element of GF(p^d) = F_p[x]/(irreducible); return
    (Q, elements as tuples, mult function, generator powers list)."""
    Q = p ** d
    # search monic degree-d polynomials for one where x generates the group
    for coeffs in itertools.product(range(p), repeat=d):
        mod = list(coeffs)  # x^d = -(c_{d-1}x^{d-1}+...+c_0)  (we store c_0..c_{d-1})

        def mul(a, b):
            prod = [0] * (2 * d - 1)
            for i, ai in enumerate(a):
                for j, bj in enumerate(b):
                    prod[i + j] = (prod[i + j] + ai * bj) % p
            for k in range(2 * d - 2, d - 1, -1):
                c = prod[k]
                if c:
                    prod[k] = 0
                    for t in range(d):
                        prod[k - d + t] = (prod[k - d + t] - c * mod[t]) % p
            return tuple(prod[:d])

        one = tuple([1] + [0] * (d - 1))
        x = tuple([0, 1] + [0] * (d - 2)) if d >= 2 else (0,)
        if d == 1:
            continue
        pw = [one]
        cur = one
        ok = True
        for _ in range(Q - 2):
            cur = mul(cur, x)
            if cur == one:
                ok = False
                break
            pw.append(cur)
        if ok and mul(cur, x) == one and len(set(pw)) == Q - 1:
            return Q, mul, pw
    raise RuntimeError("no primitive polynomial found")


def fingerprint_weights(v, p, Q, pw):
    """One trial of the construction: y_i = g^{e_i}, functional l; weight of
    model a is l(g^{s(a)}), s(a) = sum a_i e_i mod (Q-1).  Returns list over
    all a in {0,1}^v (index = binary number, bit i = a_i)."""
    e = [rng.randrange(Q - 1) for _ in range(v)]
    d = len(pw[0])
    ell = [rng.randrange(p) for _ in range(d)]
    w = []
    for idx in range(2 ** v):
        s = sum(e[i] for i in range(v) if (idx >> i) & 1) % (Q - 1)
        elt = pw[s]
        w.append(sum(c * l for c, l in zip(elt, ell)) % p)
    return w


def part1(v, p):
    L = max(1, v)
    d = 2  # an extension of degree >= 2 (a larger Q only helps detection)
    while p ** d - 1 < 2 * L:
        d += 1
    Q, mul, pw = gf_tables(p, d)
    npts = 2 ** v
    sets = list(range(2 ** npts))  # model set S as bitmask over the 2^v points

    def cnt(S, w):  # integer sum of table weights over models in S
        return sum(w[a] for a in range(npts) if (S >> a) & 1)

    # build a fixed good trial list greedily: every nonempty S detected
    trials = []
    undetected = set(sets) - {0}
    tries = 0
    while undetected:
        tries += 1
        w = fingerprint_weights(v, p, Q, pw)
        newly = {S for S in undetected if cnt(S, w) % p != 0}
        if newly:
            trials.append(w)
            undetected -= newly
        if tries > 100000:
            raise RuntimeError("trial search failed")
    r = len(trials)
    # rank (over F_p) of the trial weight vectors: detection of every nonempty
    # S needs no nonzero 0/1 vector orthogonal to all weight vectors
    span_rank = rank_mod_p(trials, p) if p > 2 else rank_f2(trials)
    out = {"v": v, "p": p, "Q": Q, "r": r, "span_rank": span_rank}
    if p == 2:
        # F_2 network read as a 0/1 network: accepting-configuration count
        # count = 1 + prod_j (1 + c_j)   (tag trick for 1 - Z, twice)
        counts_sat, counts_unsat, ok = [], [], True
        for S in sets:
            cs = [cnt(S, w) for w in trials]
            prod = 1
            for c in cs:
                prod *= (1 + c)
            count = 1 + prod
            signed = 1
            for c in cs:
                signed *= (1 - c)
            signed = 1 - signed  # same network over Z with weight -1 on tags
            sat = 1 if S else 0
            if count % 2 != sat:
                ok = False
            (counts_sat if sat else counts_unsat).append((count, signed))
        out.update(ok_mod2=ok,
                   unsat_counts=sorted({c for c, _ in counts_unsat}),
                   sat_count_min=min(c for c, _ in counts_sat),
                   sat_count_max=max(c for c, _ in counts_sat),
                   sat_signed_values=len({s for _, s in counts_sat}),
                   sat_signed_minmax=(min(s for _, s in counts_sat), max(s for _, s in counts_sat)),
                   sat_inputs_with_count_1=sum(1 for c, _ in counts_sat if c == 1),
                   per_trial_max_c=max(cnt(S, w) for S in sets for w in trials))
    else:
        # F_p Fermat version over Z: V = 1 - prod_j (1 - C_j^{p-1}), weights in {0..p-1}
        vals_sat, vals_unsat, ok = set(), set(), True
        for S in sets:
            prod = 1
            for w in trials:
                C = cnt(S, w)
                prod *= (1 - C ** (p - 1))
            V = 1 - prod
            sat = 1 if S else 0
            if V % p != sat:
                ok = False
            (vals_sat if sat else vals_unsat).add(V)
        out.update(ok_modp=ok, unsat_values=sorted(vals_unsat),
                   sat_values_count=len(vals_sat),
                   sat_values_minmax=(min(vals_sat), max(vals_sat)),
                   sat_values_equal_1=(vals_sat == {1}))
    return out, trials

# --------------------------------------------- constraint networks + cuts
class Net:
    """Boolean constraint network: variables 0..nv-1 (first n are inputs),
    constraints = (scope tuple, predicate on the tuple of values).  count(x) =
    number of aux assignments satisfying all constraints."""

    def __init__(self, n, nv, cons):
        self.n, self.nv, self.cons = n, nv, cons


def factorise(net, A_inputs, side_var, side_con):
    """Cut factorisation.  side_var[u] in {0,1} for every variable (inputs
    fixed by A_inputs), side_con[k] in {0,1}.  Returns (crossing list,
    alpha dict, beta dict) with alpha[(xA, sigma)] counts."""
    n, nv, cons = net.n, net.nv, net.cons
    cross = set()
    for k, (scope, _) in enumerate(cons):
        for u in scope:
            if side_var[u] != side_con[k]:
                cross.add(u)
    cross = sorted(cross)
    res = []
    for side in (0, 1):
        ins = [i for i in range(n) if side_var[i] == side]
        aux = [u for u in range(n, nv) if side_var[u] == side and u not in cross]
        own_cross = [u for u in cross if side_var[u] == side]
        other_cross = [u for u in cross if side_var[u] != side]
        my_cons = [cons[k] for k in range(len(cons)) if side_con[k] == side]
        table = {}
        free = [u for u in own_cross if u >= n] + aux + other_cross
        for xs in itertools.product((0, 1), repeat=len(ins)):
            val = [None] * nv
            for i, b in zip(ins, xs):
                val[i] = b
            for fs in itertools.product((0, 1), repeat=len(free)):
                for u, b in zip(free, fs):
                    val[u] = b
                if all(pred(tuple(val[u] for u in scope)) for scope, pred in my_cons):
                    sigma = tuple(val[u] for u in cross)
                    key = (xs, sigma)
                    table[key] = table.get(key, 0) + 1
        res.append((ins, table))
    return cross, res


def check_cut(net, f, A_inputs, side_var, side_con, count_fn=None):
    cross, ((insA, alpha), (insB, beta)) = factorise(net, A_inputs, side_var, side_con)
    c = len(cross)
    # group by sigma
    by_sigma_A, by_sigma_B = {}, {}
    for (xs, sg), a in alpha.items():
        by_sigma_A.setdefault(sg, {})[xs] = a
    for (xs, sg), b in beta.items():
        by_sigma_B.setdefault(sg, {})[xs] = b
    rowsA = list(itertools.product((0, 1), repeat=len(insA)))
    rowsB = list(itertools.product((0, 1), repeat=len(insB)))
    ident_ok = True
    maxmult = 0
    M = []
    for xa in rowsA:
        row = []
        for xb in rowsB:
            x = [None] * net.n
            for i, b in zip(insA, xa):
                x[i] = b
            for i, b in zip(insB, xb):
                x[i] = b
            tot = 0
            nz = 0
            for sg in set(by_sigma_A) & set(by_sigma_B):
                t = by_sigma_A[sg].get(xa, 0) * by_sigma_B[sg].get(xb, 0)
                tot += t
                nz += 1 if t else 0
            maxmult = max(maxmult, nz)
            fx = f(tuple(x))
            cx = count_fn(tuple(x)) if count_fn else net_count(net, tuple(x))
            if tot != cx:
                ident_ok = False
            row.append(fx)
        M.append(row)
    return c, ident_ok, maxmult, M


_count_cache = {}


def net_count(net, x):
    key = (id(net), x)
    if key in _count_cache:
        return _count_cache[key]
    n, nv = net.n, net.nv
    tot = 0
    for zs in itertools.product((0, 1), repeat=nv - n):
        val = list(x) + list(zs)
        if all(pred(tuple(val[u] for u in scope)) for scope, pred in net.cons):
            tot += 1
    _count_cache[key] = tot
    return tot


OPS = [lambda a, b, t=t: (t >> (2 * a + b)) & 1 for t in range(16)]


def random_circuit_verifier(n, G):
    """Random fan-in-2 circuit with arbitrary 2-input gates and fanout; the
    verifier guesses every gate value (aux vars n..n+G-1) and checks locally,
    plus output = 1.  Unambiguous: count(x) = C(x)."""
    gates = []
    for k in range(G):
        a = rng.randrange(n + k)
        b = rng.randrange(n + k)
        t = rng.randrange(16)
        gates.append((a, b, t))
    cons = []
    for k, (a, b, t) in enumerate(gates):
        g = n + k
        cons.append(((a, b, g), (lambda vals, t=t: OPS[t](vals[0], vals[1]) == vals[2])))
    cons.append(((n + G - 1,), (lambda vals: vals[0] == 1)))
    net = Net(n, n + G, cons)

    def f(x):
        val = list(x)
        for (a, b, t) in gates:
            val.append(OPS[t](val[a], val[b]))
        return val[-1]
    return net, f


def crossing(net, side_var, side_con):
    cr = set()
    for k, (scope, _) in enumerate(net.cons):
        for u in scope:
            if side_var[u] != side_con[k]:
                cr.add(u)
    return len(cr)


def local_min_cut(net, side_var, side_con, rounds=4):
    """Greedy single flips of aux variables / constraints that lower the
    crossing count (inputs stay on their sides)."""
    sv, sc = list(side_var), list(side_con)
    best = crossing(net, sv, sc)
    for _ in range(rounds):
        improved = False
        for u in range(net.n, net.nv):
            sv[u] ^= 1
            c = crossing(net, sv, sc)
            if c < best:
                best, improved = c, True
            else:
                sv[u] ^= 1
        for k in range(len(sc)):
            sc[k] ^= 1
            c = crossing(net, sv, sc)
            if c < best:
                best, improved = c, True
            else:
                sc[k] ^= 1
        if not improved:
            break
    return sv, sc


def part2(trials=200, n=8, G=10, brute=20):
    stats = {"cases": 0, "identity_fail": 0, "mult_gt1": 0, "rankQ_gt_2c": 0,
             "rankF2_gt_2c": 0, "rankQ_ne_rankF2": 0, "max_c": 0, "tight_cases": 0,
             "brute_force_unambiguity_checked": 0, "brute_force_unambiguity_fail": 0,
             "c_hist": {}}
    for t in range(trials):
        net, f = random_circuit_verifier(n, G)
        if t < brute:  # independent check that the verifier is unambiguous
            _count_cache.clear()  # cache is keyed by id(net); ids are reused
            stats["brute_force_unambiguity_checked"] += 1
            for x in itertools.product((0, 1), repeat=n):
                if net_count(net, x) != f(x):
                    stats["brute_force_unambiguity_fail"] += 1
                    break
        A = set(rng.sample(range(n), n // 2))
        side_var = [0 if i in A else 1 for i in range(n)] + [rng.randrange(2) for _ in range(G)]
        side_con = [rng.randrange(2) for _ in net.cons]
        side_var, side_con = local_min_cut(net, side_var, side_con)
        c, ok, mult, M = check_cut(net, f, A, side_var, side_con, count_fn=f)
        stats["c_hist"][c] = stats["c_hist"].get(c, 0) + 1
        rq = rank_q_exact(M)
        r2 = rank_f2(M)
        stats["cases"] += 1
        stats["identity_fail"] += (not ok)
        stats["mult_gt1"] += (mult > 1)
        stats["rankQ_gt_2c"] += (rq > 2 ** c)
        stats["rankF2_gt_2c"] += (r2 > 2 ** c)
        stats["rankQ_ne_rankF2"] += (rq != r2)
        stats["max_c"] = max(stats["max_c"], c)
        stats["tight_cases"] += (rq == 2 ** c)
        stats["slack_hist"] = stats.get("slack_hist", {})
        sl = c - (rq.bit_length() - 1 if rq else 0)  # c - floor(log2 rank_Q)
        stats["slack_hist"][sl] = stats["slack_hist"].get(sl, 0) + 1
    return stats


def trial_net(v, W):
    """One F_2 trial at the clause-split cut.  Inputs: S_A (2^v bits, side A),
    S_B (2^v bits, side B).  Aux: a in {0,1}^v.  A-constraint: S_A[a] and W[a];
    B-constraint: S_B[a].  count = |S_A & S_B & W|."""
    m = 2 ** v
    n = 2 * m
    nv = n + v

    def idx(vals):
        return sum(b << i for i, b in enumerate(vals))
    consA = (tuple(range(0, m)) + tuple(range(n, nv)),
             (lambda vals: vals[idx(vals[m:])] == 1 and W[idx(vals[m:])] == 1))
    consB = (tuple(range(m, 2 * m)) + tuple(range(n, nv)),
             (lambda vals: vals[idx(vals[m:])] == 1))
    net = Net(n, nv, [consA, consB])
    side_var = [0] * m + [1] * m + [0] * v  # a on Alice's side
    side_con = [0, 1]

    def parity(x):
        SA, SB = x[:m], x[m:]
        return sum(1 for t in range(m) if SA[t] and SB[t] and W[t]) % 2
    return net, side_var, side_con, parity


def part3(v, W):
    net, side_var, side_con, parity = trial_net(v, W)
    m = 2 ** v
    A = set(range(m))
    def count_fn(x):
        SA, SB = x[:m], x[m:]
        return sum(1 for t in range(m) if SA[t] and SB[t] and W[t])
    c, ok, mult, Mpar = check_cut(net, parity, A, side_var, side_con, count_fn=count_fn)
    r2 = rank_f2(Mpar)
    rq_lower = rank_mod_p(Mpar)
    # max witness count of the trial
    return {"v": v, "W_size": sum(W), "crossing_c": c, "identity_count_ok": ok,
            "max_nonzero_sigmas_per_input": mult, "rank_F2_parity": r2,
            "rank_Q_parity_lower": rq_lower, "two_pow_c": 2 ** c}


def part4(v, r):
    m = 2 ** v
    M = [[1 if (S & T) else 0 for T in range(2 ** m)] for S in range(2 ** m)]
    r2 = rank_f2(M)
    rq_lower = rank_mod_p(M)
    zero_rows = sum(1 for row in M if not any(row))
    return {"v": v, "rank_F2_SAT": r2, "rank_Q_SAT_lower": rq_lower,
            "rank_Q_SAT_upper(rows-zero_rows)": len(M) - zero_rows,
            "log2_rank": round(np.log2(max(1, rq_lower)), 3),
            "full_construction_crossing_at_least_r*v": r * v}


def tagged_network(v, trials):
    """Explicit 0/1 network for the F_2 construction's exact OR, built as a
    constraint network and counted by brute force (Part 1b).  Inputs: model
    set S (2^v bits).  Aux: final tag F, one tag t_j per factor (1 - z_j), one
    guessed model a^(j) per trial.  Lines 55-61 of the exact-network note:
    on a constant branch every unused guess is pinned to zero (weight 1);
    the other branch carries the computed value (weight -1 = 1 over F_2)."""
    m = 2 ** v
    r = len(trials)
    n = m
    Fv = n
    T = [n + 1 + j for j in range(r)]
    Ab = [[n + 1 + r + j * v + i for i in range(v)] for j in range(r)]
    nv = n + 1 + r + r * v
    inner = T + [b for blk in Ab for b in blk]
    cons = [((Fv,) + tuple(inner), lambda vals: vals[0] == 1 or not any(vals[1:]))]
    for j in range(r):
        W = trials[j]
        cons.append(((Fv, T[j]) + tuple(Ab[j]),
                     lambda vals: not (vals[0] == 1 and vals[1] == 0) or not any(vals[2:])))

        def trial_ok(vals, W=W):
            if not (vals[0] == 1 and vals[1] == 1):
                return True
            a = sum(b << i for i, b in enumerate(vals[2:2 + v]))
            return vals[2 + v + a] == 1 and W[a] == 1
        cons.append(((Fv, T[j]) + tuple(Ab[j]) + tuple(range(m)), trial_ok))
    return Net(n, nv, cons)


def part1b(v, trials):
    _count_cache.clear()
    net = tagged_network(v, trials)
    m = 2 ** v
    mism_formula = 0
    mism_parity = 0
    counts_unsat, counts_sat = set(), []
    for S in itertools.product((0, 1), repeat=m):
        cnt_bf = net_count(net, S)
        cs = [sum(1 for a in range(m) if S[a] and w[a]) for w in trials]
        prod = 1
        for c in cs:
            prod *= 1 + c
        mism_formula += (cnt_bf != 1 + prod)
        sat = 1 if any(S) else 0
        mism_parity += (cnt_bf % 2 != sat)
        (counts_sat.append(cnt_bf) if sat else counts_unsat.add(cnt_bf))
    return {"v": v, "r": len(trials), "aux_bits": net.nv - net.n,
            "formula_mismatches": mism_formula, "parity_mismatches": mism_parity,
            "unsat_counts_bruteforce": sorted(counts_unsat),
            "sat_counts_bruteforce_minmax": (min(counts_sat), max(counts_sat)),
            "sat_inputs_with_count_1": sum(1 for c in counts_sat if c == 1)}


def part5(n=6):
    """Additivity test: inner product mod 2 on (x_1..x_n, y_1..y_n), prefix
    cuts A_t = {x_1..x_t}.  A deterministic (hence unambiguous) circuit has
    2n-1 gates, yet sum_t log2 rank_Q(M^{(t)}) grows quadratically."""
    out = []
    total = 0.0
    for t in range(1, n + 1):
        rows = list(itertools.product((0, 1), repeat=t))
        cols = list(itertools.product((0, 1), repeat=(n - t) + n))
        M = []
        for xa in rows:
            row = []
            for rest in cols:
                x = list(xa) + list(rest[: n - t])
                y = rest[n - t:]
                row.append(sum(a & b for a, b in zip(x, y)) % 2)
            M.append(row)
        rq = rank_mod_p(M)
        out.append((t, rq))
        total += float(np.log2(rq)) if rq else 0.0
    return {"n": n, "rank_Q_lower_by_cut": out, "sum_log2_rank": round(total, 2),
            "deterministic_gates": 2 * n - 1}


if __name__ == "__main__":
    print("Part 1: witness counts of the quadratic construction (all model sets)")
    trial_lists = {}
    for v in (1, 2, 3):
        out, trials = part1(v, 2)
        trial_lists[v] = trials
        print("  ", out)
    for v in (1, 2):
        out, _ = part1(v, 3)
        print("  ", out)
    print("Part 1b: the tagged F_2 network built explicitly, counts by brute force")
    for v in (1, 2):
        print("  ", part1b(v, trial_lists[v]))
    print("Part 2: positive cut factorisation on guess-all-gates verifiers")
    print("  ", part2())
    print("Part 3: one F_2 trial at the clause-split cut")
    for v in (2, 3):
        W = [1 if t else 0 for t in trial_lists[v][0]]
        print("   fingerprint trial:", part3(v, W))
        print("   all-ones weights :", part3(v, [1] * (2 ** v)))
    print("Part 4: SAT verdict at the clause-split cut")
    for v in (2, 3):
        print("  ", part4(v, len(trial_lists[v])))
    print("Part 5: additivity over cuts fails for a linear deterministic circuit")
    for n in (4, 6, 8):
        print("  ", part5(n))
