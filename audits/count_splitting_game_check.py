#!/usr/bin/env python3
"""Exact evaluation of the alternating counting games of
counting-sat-under-a-quasi-linear-sat-solver.md on toy CNFs.

Nothing here is randomized except the choice of test formulas (fixed seeds).
Every game value is computed by exhaustive OR/AND evaluation and compared with a
brute-force model count.

Part A  integer count-splitting game, literal enumeration of every prover message
        (n=4 variables, k=2 blocks of s=2).
Part B  integer count-splitting game, exact evaluation by sumsets (the existential
        choice of a message (v_y) with sum = claim and every child winning is
        exactly "claim lies in the sumset of the per-child winning sets").
        Sizes n up to 12, block sizes s in {1,2,3,4}.
Part C  algebraic block sum-check over a SMALL prime field F_q with q > d (the
        individual degree), every prover table enumerated, every challenge in
        F_q^s enumerated: the game accepts exactly the claims = #phi mod q.
        Shows that a field of size d+1 suffices for exactness of the alternating
        form (Schwartz-Zippel's q > d*n is only needed for the randomized protocol).
Part D  exponent optimisation for the stripping recursion (pure arithmetic).
"""
import itertools, random, math, sys
from functools import lru_cache

# ---------------------------------------------------------------- formulas
def random_cnf(n, m, width=3, max_occ=None, seed=0):
    rng = random.Random(seed)
    occ = [0] * n
    clauses = []
    tries = 0
    while len(clauses) < m and tries < 10000:
        tries += 1
        avail = [v for v in range(n) if max_occ is None or occ[v] < max_occ]
        if len(avail) < 1:
            break
        w = min(width, len(avail))
        vs = rng.sample(avail, w)
        for v in vs:
            occ[v] += 1
        clauses.append(tuple((v, rng.random() < 0.5) for v in vs))  # (var, negated?)
    return clauses

def phi(clauses, x):  # x: tuple of 0/1 of length n
    for cl in clauses:
        if not any((x[v] == 0) if neg else (x[v] == 1) for v, neg in cl):
            return 0
    return 1

def brute_count(clauses, n):
    return sum(phi(clauses, x) for x in itertools.product((0, 1), repeat=n))

# ---------------------------------------------------------------- Part A
def game_literal(clauses, n, s, claim):
    """Literal Sigma_{2k} evaluation: OR over every message vector (all entries
    in [0, 2^{remaining}]), AND over every universal block choice y."""
    k = n // s
    memo = {}  # a subgame's value depends only on (round, prefix, claim)
    def val(i, prefix, c):
        if (i, prefix, c) not in memo:
            memo[(i, prefix, c)] = val_raw(i, prefix, c)
        return memo[(i, prefix, c)]
    def val_raw(i, prefix, c):
        if i == k:
            return c == phi(clauses, prefix)
        rem = n - (i + 1) * s
        for v in itertools.product(range(2 ** rem + 1), repeat=2 ** s):
            if sum(v) != c:
                continue            # verifier's sum check rejects
            ok = True
            for yi, y in enumerate(itertools.product((0, 1), repeat=s)):
                if not val(i + 1, prefix + y, v[yi]):
                    ok = False      # universal player found a rejecting branch
                    break
            if ok:
                return True
        return False
    return val(0, (), claim)

# ---------------------------------------------------------------- Part B
def winning_claims(clauses, n, s):
    """Set of root claims c for which the existential player wins, computed
    exactly via sumsets, for blocks of size s (last block may be shorter)."""
    blocks = []
    left = n
    while left > 0:
        b = min(s, left); blocks.append(b); left -= b
    k = len(blocks)
    memo = {}
    def W(i, prefix):
        key = (i, prefix)
        if key in memo:
            return memo[key]
        if i == k:
            res = frozenset([phi(clauses, prefix)])
        else:
            rem = n - sum(blocks[: i + 1])
            acc = {0}
            for y in itertools.product((0, 1), repeat=blocks[i]):
                child = [c for c in W(i + 1, prefix + y) if 0 <= c <= 2 ** rem]
                acc = {a + c for a in acc for c in child}
            res = frozenset(acc)
        memo[key] = res
        return res
    return W(0, ())

# ---------------------------------------------------------------- Part C
def poly_eval_table(table, d, s, q, r):
    """Evaluate the unique polynomial of individual degree <= d given by its
    values on the grid {0..d}^s at a point r in F_q^s (successive Lagrange)."""
    vals = list(table)
    nodes = list(range(d + 1))
    for j in range(s):  # contract the first remaining coordinate
        x = r[j]
        lag = []
        for a in nodes:
            num, den = 1, 1
            for b in nodes:
                if b != a:
                    num = num * (x - b) % q
                    den = den * (a - b) % q
            lag.append(num * pow(den, q - 2, q) % q)
        stride = (d + 1) ** (s - j - 1)
        new = []
        for blk in range(0, len(vals), stride * (d + 1)):
            for t in range(stride):
                new.append(sum(lag[a] * vals[blk + a * stride + t] for a in range(d + 1)) % q)
        vals = new
    return vals[0]

def arith_P(clauses, point, q):
    """Arithmetisation prod_j (1 - prod_{l in C_j} (1 - l(x))) over F_q."""
    out = 1
    for cl in clauses:
        t = 1
        for v, neg in cl:
            lit = (1 - point[v]) if neg else point[v]
            t = t * (1 - lit) % q
        out = out * (1 - t) % q
    return out

def algebraic_game_accepts(clauses, n, s, d, q):
    """Return the set of claims in F_q accepted by the exhaustively evaluated
    block sum-check game: exists table g on {0..d}^s with Boolean sum = claim,
    for all r in F_q^s the subgame at claim g(r) is won."""
    k = n // s
    grid = list(itertools.product(range(d + 1), repeat=s))
    bool_idx = [gi for gi, g in enumerate(grid) if all(c in (0, 1) for c in g)]
    pts = list(itertools.product(range(q), repeat=s))
    tables = list(itertools.product(range(q), repeat=len(grid)))
    # precompute evaluations of every table at every point (shared across states)
    evals = [[poly_eval_table(t, d, s, q, r) for r in pts] for t in tables]
    bsum = [sum(t[i] for i in bool_idx) % q for t in tables]
    memo = {}
    def acc(i, prefix):
        if (i, prefix) in memo:
            return memo[(i, prefix)]
        if i == k:
            res = frozenset([arith_P(clauses, prefix, q)])
        else:
            child = [acc(i + 1, prefix + r) for r in pts]
            res = set()
            for ti in range(len(tables)):
                if all(evals[ti][ri] in child[ri] for ri in range(len(pts))):
                    res.add(bsum[ti])
            res = frozenset(res)
        memo[(i, prefix)] = res
        return res
    return acc(0, ())

# ---------------------------------------------------------------- Part D
def best_exponent(n, a, logK=1.0, extra_bits=0.0):
    """Minimise over k the log2 running time of the stripping recursion:
    E(k) = s + 2k*(a*log2 L + logK) with s = ceil(n/k) + log2(n+1) (message bits)
    and L = log2 of the largest formula, iterated to a fixed point."""
    def E_of(k):
        s = math.ceil(n / k)
        base = s + math.log2(n + 1) + extra_bits
        L = base
        for _ in range(12):
            E = base + 2 * k * (a * math.log2(max(L, 2.0)) + logK)
            L = E + 3 * math.log2(max(E, 2.0))  # formula bits ~ H L^3
        return E, k, s
    ks = sorted(set([max(1, int(round(1.003 ** j))) for j in range(0, 7000)] ))
    ks = [k for k in ks if k <= n]
    best = min(E_of(k) for k in ks)
    lo, hi = max(1, int(best[1] * 0.99) - 2), min(n, int(best[1] * 1.01) + 2)
    return min(min(E_of(k) for k in range(lo, hi + 1)), best)

def main():
    print("Part A: literal enumeration, n=4, s=2 (k=2)")
    for seed in range(6):
        cl = random_cnf(4, 5, max_occ=4, seed=seed)
        true = brute_count(cl, 4)
        acc = [c for c in range(17) if game_literal(cl, 4, 2, c)]
        print(f"  seed {seed}: brute #phi={true:2d}  accepted claims={acc}  {'OK' if acc == [true] else 'FAIL'}")
        assert acc == [true]

    print("Part B: sumset evaluation, bounded occurrence (<=3) 3-CNF")
    for n, m in [(6, 6), (8, 8), (10, 9), (12, 11)]:
        for s in (1, 2, 3, 4):
            for seed in range(3):
                cl = random_cnf(n, m, max_occ=3, seed=100 * n + seed)
                true = brute_count(cl, n)
                W = winning_claims(cl, n, s)
                ok = (W == frozenset([true]))
                assert ok, (n, s, seed, true, sorted(W)[:10])
            print(f"  n={n:2d} m={m:2d} s={s}: 3 formulas, winning root claims == {{brute count}}: OK")

    print("Part C: algebraic block sum-check over tiny fields (every table, every challenge)")
    cases = [(4, 1, 3, 5), (4, 1, 3, 7), (4, 2, 2, 3), (3, 1, 2, 3)]
    for n, s, d, q in cases:
        for seed in range(3):
            cl = random_cnf(n, 6, max_occ=d, seed=7 * seed + n + s)
            true = brute_count(cl, n)
            A = algebraic_game_accepts(cl, n, s, d, q)
            ok = (A == frozenset([true % q]))
            print(f"  n={n} s={s} d={d} q={q} seed={seed}: #phi={true:2d}, #phi mod q={true % q}, accepted={sorted(A)}  {'OK' if ok else 'FAIL'}")
            assert ok

    print("Part D: optimal k for the stripping recursion, log2 time E (a = 3 + c)")
    print("     n      a    k*    s*   E(k*)    2*sqrt(a n log2 n)   n/sqrt(log2 n)")
    for n in (10**3, 10**4, 10**5, 10**6, 10**8):
        for a in (3, 4, 6):
            E, k, s = best_exponent(n, a)
            print(f"  {n:>8d}  {a:>3d}  {k:>5d}  {s:>6d}  {E:>9.0f}   {2*math.sqrt(a*n*math.log2(n)):>12.0f}   {n/math.sqrt(math.log2(n)):>12.0f}")

if __name__ == "__main__":
    main()
