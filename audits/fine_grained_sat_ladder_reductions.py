#!/usr/bin/env python3
"""
Conjecture-ladder reductions to proper DIMACS 3-CNF, for
conditional-sat-deadlines-from-fine-grained-conjectures.md.

Source problems, each encoded exactly as stated in the cited source:
  tri   : triangle detection in a simple undirected graph with m edges
          (Abboud & Vassilevska Williams 2014, arXiv:1402.0054, Conjecture 4).
  sum3  : AVW14 Conjecture 1: a set S of n distinct integers in [-n^3, n^3];
          are there three distinct elements a, b, c of S with a + b = c?
  ksum  : Abboud, Lewi & Williams 2014 (arXiv:1311.3054), Definition 1.1 with
          target 0 and range [-M, M] (their footnote 1), M = n^(2k): n integers,
          repetitions allowed; is there an index set of size k with sum 0?
  klist : Abboud & Lewi 2013 (arXiv:1304.7558), Definition 2: k lists of n
          integers; is there one number from each list with sum 0?

Encoding (one primitive): k lookups into PUBLIC tables, each through a one-hot
selector s_1..s_R with binary implications  s_r -> (Y_t = table[r][t]).  A
prefix-OR chain p_r -> p_{r-1} or s_r gives "at least one" (unit p_R) and the
index order s'_b -> p_{b-1}.  Sums are checked with width-3 ripple-carry adders
mod 2^L, where 2^L exceeds the largest possible |sum|, followed by "all sum bits
are 0".  Three false anchors are pinned by the seven proper clauses on them;
shorter clauses are padded with positive anchor literals.  Every clause has
exactly three distinct variables and every variable 1..V occurs.

CaDiCaL is found on PATH or in a Lean toolchain (as in seed_chart_forced_memory_audit.py);
each formula is piped to it on stdin.

Usage:  python3 fine_grained_sat_ladder_reductions.py check       # brute force vs CaDiCaL (default)
        python3 fine_grained_sat_ladder_reductions.py lengths     # encoded-length table
        python3 fine_grained_sat_ladder_reductions.py constants   # explicit length constants
"""
import itertools
import math
import os
import random
import subprocess
import sys
import tempfile
from array import array

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


# ----------------------------------------------------------------------------
# CNF container
# ----------------------------------------------------------------------------
class CNF:
    def __init__(self):
        self.nv = 0
        self.lits = array("i")          # flat, three literals per clause
        self.F = [self.new(), self.new(), self.new()]
        for mask in range(1, 8):        # forbid every nonzero anchor assignment
            self.lits.extend((-self.F[i] if (mask >> i) & 1 else self.F[i])
                             for i in range(3))

    @property
    def ncl(self):
        return len(self.lits) // 3

    def new(self):
        self.nv += 1
        return self.nv

    def vec(self, w):
        return [self.new() for _ in range(w)]

    def add(self, lits):
        vs = [abs(l) for l in lits]
        assert len(set(vs)) == len(vs), lits
        lits = list(lits)
        for f in self.F:                # pad with positive false anchors
            if len(lits) >= 3:
                break
            if f not in vs:
                lits.append(f)
        assert len(lits) == 3
        self.lits.extend(lits)

    def false_clause(self):             # the disjunction of the three anchors
        self.lits.extend(self.F)

    def dimacs(self):
        out = ["p cnf %d %d\n" % (self.nv, self.ncl)]
        L = self.lits
        out += ["%d %d %d 0\n" % (L[i], L[i + 1], L[i + 2])
                for i in range(0, len(L), 3)]
        return "".join(out)

    def nbits(self):
        """Exact encoded length N in bits (8 per ASCII byte) without building the text."""
        n = len("p cnf %d %d\n" % (self.nv, self.ncl))
        # each clause line "a b c 0\n": len(a)+len(b)+len(c) + 3 spaces + "0\n"
        dl = {}
        tot = 0
        for l in self.lits:
            x = dl.get(l)
            if x is None:
                x = len(str(l))
                dl[l] = x
            tot += x
        n += tot + 5 * self.ncl
        return 8 * n


def bits(x, L):
    """Two's complement of x mod 2^L, least significant bit first."""
    y = x % (1 << L)
    return [(y >> t) & 1 for t in range(L)]


# ----------------------------------------------------------------------------
# Gadgets
# ----------------------------------------------------------------------------
def lookup(f, table, Y):
    """One-hot selector over a public table; s_r -> Y equals record r."""
    s = f.vec(len(table))
    for r, rec in enumerate(table):
        assert len(rec) == len(Y)
        for t, bit in enumerate(rec):
            f.add([-s[r], Y[t] if bit else -Y[t]])
    return s


def prefix(f, s):
    """p_r -> (p_{r-1} or s_r), p_0 -> s_0.  p_r true implies some s_{r'} (r' <= r) true."""
    p = f.vec(len(s))
    f.add([-p[0], s[0]])
    for r in range(1, len(s)):
        f.add([-p[r], p[r - 1], s[r]])
    return p


def after(f, s_next, p_prev):
    """s_next[b] -> some selector of the previous lookup with index < b is true."""
    f.add([-s_next[0]])
    for b in range(1, len(s_next)):
        f.add([-s_next[b], p_prev[b - 1]])


def xor(f, a, b):
    z = f.new()
    f.add([-z, a, b]); f.add([-z, -a, -b]); f.add([z, -a, b]); f.add([z, a, -b])
    return z


def maj(f, a, b, c):
    o = f.new()
    f.add([-a, -b, o]); f.add([-a, -c, o]); f.add([-b, -c, o])
    f.add([a, b, -o]); f.add([a, c, -o]); f.add([b, c, -o])
    return o


def adder(f, X, Y):
    """Ripple-carry sum mod 2^L (LSB first); carry-in is the false anchor F[0].
    Per bit: 3 new variables, 14 clauses."""
    cin = f.F[0]
    Z = []
    for t in range(len(X)):
        u = xor(f, X[t], Y[t])
        s = xor(f, u, cin)
        c = maj(f, X[t], Y[t], cin)
        Z.append(s)
        cin = c
    return Z


# ----------------------------------------------------------------------------
# Builders.  Each returns (cnf, decode) where decode(model_true_set) -> witness.
# ----------------------------------------------------------------------------
def build_tri(n, edges):
    E = sorted({(min(u, v), max(u, v)) for (u, v) in edges if u != v})
    l = max(1, (n - 1).bit_length())
    f = CNF()
    if not E:
        f.false_clause()
        return f, E, None
    A, B, C = f.vec(l), f.vec(l), f.vec(l)
    tab = [bits(u, l) + bits(v, l) for (u, v) in E]
    s1 = lookup(f, tab, A + B)
    s2 = lookup(f, tab, B + C)
    s3 = lookup(f, tab, A + C)
    for s in (s1, s2, s3):
        p = prefix(f, s)
        f.add([p[-1]])

    def decode(T):
        def val(V):
            return sum(1 << t for t, v in enumerate(V) if v in T)
        a, b, c = val(A), val(B), val(C)
        return (a, b, c), [[E[r] for r, v in enumerate(s) if v in T] for s in (s1, s2, s3)]
    return f, E, decode


def closed_tri(m, n):
    l = max(1, (n - 1).bit_length())
    return 3 + 3 * l + 6 * m, 10 + 6 * m * l + 3 * m


def build_sum3(S):
    n = len(S)
    assert len(set(S)) == n, "AVW14 Conjecture 1 is about a set"
    M = n ** 3
    assert all(abs(x) <= M for x in S)
    L = (3 * M).bit_length()            # 2^L > 3 n^3 >= |a + b - c|
    f = CNF()
    Y1, Y2, Y3 = f.vec(L), f.vec(L), f.vec(L)
    s1 = lookup(f, [bits(x, L) for x in S], Y1)
    s2 = lookup(f, [bits(x, L) for x in S], Y2)
    s3 = lookup(f, [bits(-x, L) for x in S], Y3)     # stores -c
    p1, p2, p3 = prefix(f, s1), prefix(f, s2), prefix(f, s3)
    after(f, s2, p1)                    # index(a) < index(b): a + b = b + a
    for r in range(n):                  # c is neither a nor b
        f.add([-s1[r], -s3[r]])
        f.add([-s2[r], -s3[r]])
    f.add([p2[-1]])
    f.add([p3[-1]])
    W = adder(f, adder(f, Y1, Y2), Y3)
    for z in W:
        f.add([-z])

    def decode(T):
        return [[r for r, v in enumerate(s) if v in T] for s in (s1, s2, s3)]
    return f, L, decode


def closed_sum3(n):
    L = (3 * n ** 3).bit_length()
    return 3 + 9 * L + 6 * n, 9 + 3 * n * L + 6 * n + 29 * L, L


def build_ksum(xs, k, M=None):
    n = len(xs)
    if M is None:
        M = n ** (2 * k)
    assert all(abs(x) <= M for x in xs)
    L = (k * M).bit_length()            # 2^L > k M >= |sum|
    f = CNF()
    Ys = [f.vec(L) for _ in range(k)]
    tab = [bits(x, L) for x in xs]
    ss = [lookup(f, tab, Y) for Y in Ys]
    ps = [prefix(f, s) for s in ss]
    for j in range(1, k):
        after(f, ss[j], ps[j - 1])      # i_1 < i_2 < ... < i_k
    f.add([ps[-1][-1]])
    Z = Ys[0]
    for j in range(1, k):
        Z = adder(f, Z, Ys[j])
    for z in Z:
        f.add([-z])

    def decode(T):
        sel = [[r for r, v in enumerate(s) if v in T] for s in ss]
        idx = [max(sel[-1])]
        for j in range(k - 2, -1, -1):  # walk the prefix chains backwards
            idx.append(max(r for r in sel[j] if r < idx[-1]))
        return idx[::-1]
    return f, L, decode


def closed_ksum(n, k, M=None):
    if M is None:
        M = n ** (2 * k)
    L = (k * M).bit_length()
    return 3 + (4 * k - 3) * L + 2 * k * n, 8 + k * n * L + (2 * k - 1) * n + (14 * k - 13) * L, L


def closed_klist(n, k, M):
    """k lists of n entries each, range [-M, M]."""
    L = (k * M).bit_length()
    return 3 + (4 * k - 3) * L + 2 * k * n, 7 + k * n * L + k * n + k + (14 * k - 13) * L, L


def build_klist(lists, M):
    k = len(lists)
    assert all(abs(x) <= M for lst in lists for x in lst), "values outside [-M, M]"
    L = (k * M).bit_length()
    f = CNF()
    Ys = [f.vec(L) for _ in range(k)]
    ss = [lookup(f, [bits(x, L) for x in lst], Y) for lst, Y in zip(lists, Ys)]
    for s in ss:
        f.add([prefix(f, s)[-1]])
    Z = Ys[0]
    for j in range(1, k):
        Z = adder(f, Z, Ys[j])
    for z in Z:
        f.add([-z])

    def decode(T):
        return [[r for r, v in enumerate(s) if v in T] for s in ss]
    return f, L, decode


# ----------------------------------------------------------------------------
# Brute force from the problem definitions (not from the formulas)
# ----------------------------------------------------------------------------
def brute_tri(n, edges):
    Es = {(min(u, v), max(u, v)) for (u, v) in edges if u != v}
    return any((a, b) in Es and (b, c) in Es and (a, c) in Es
               for a, b, c in itertools.combinations(range(n), 3))


def brute_sum3(S):
    n = len(S)
    return any(S[i] + S[j] == S[k]
               for i, j, k in itertools.permutations(range(n), 3))


def brute_ksum(xs, k):
    return any(sum(xs[i] for i in c) == 0 for c in itertools.combinations(range(len(xs)), k))


def brute_klist(lists):
    return any(sum(t) == 0 for t in itertools.product(*lists))


# ----------------------------------------------------------------------------
# Proper-format check and solver call
# ----------------------------------------------------------------------------
def check_proper(text, V, C):
    lines = text.split("\n")
    assert lines[-1] == ""
    assert lines[0] == "p cnf %d %d" % (V, C)
    body = lines[1:-1]
    assert len(body) == C
    seen = set()
    keys = set()
    for ln in body:
        t = ln.split(" ")
        assert len(t) == 4 and t[3] == "0", ln
        lits = [int(x) for x in t[:3]]
        assert [str(x) for x in lits] == t[:3]           # canonical decimal
        vs = [abs(x) for x in lits]
        assert len(set(vs)) == 3 and all(1 <= v <= V for v in vs), ln
        key = tuple(sorted(lits))
        assert key not in keys, "duplicate clause " + ln
        keys.add(key)
        seen.update(vs)
    assert seen == set(range(1, V + 1)), "some variable does not occur"


def solve(f):
    text = f.dimacs()
    check_proper(text, f.nv, f.ncl)
    assert 8 * len(text) == f.nbits()
    r = subprocess.run([CADICAL, "-q"], input=text, capture_output=True, text=True)
    if r.returncode == 20:
        return None
    assert r.returncode == 10, r.stdout + r.stderr
    T = set()
    for line in r.stdout.splitlines():
        if line.startswith("v "):
            T.update(v for v in map(int, line[2:].split()) if v > 0)
    return T


# ----------------------------------------------------------------------------
# Test drivers
# ----------------------------------------------------------------------------
def run_checks(seed=20261127):
    rng = random.Random(seed)
    stats = {}

    def rec(name, truth, ok_closed):
        d = stats.setdefault(name, [0, 0, 0])
        d[0] += 1
        d[1] += truth
        d[2] += ok_closed

    # ---- triangle ----
    cases = []
    for n in range(1, 9):
        for _ in range(40):
            pairs = list(itertools.combinations(range(n), 2))
            q = rng.random()
            E = [e for e in pairs if rng.random() < q]
            cases.append((n, E))
    cases += [(3, [(0, 1), (1, 2)]), (3, [(0, 1), (1, 2), (0, 2)]), (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
              (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), (2, [(0, 1)]), (6, [])]
    for n, E in cases:
        f, Es, decode = build_tri(n, E)
        truth = brute_tri(n, E)
        T = solve(f)
        assert (T is not None) == truth, (n, E)
        if T is not None:
            (a, b, c), sel = decode(T)
            assert a < b < c < n and (a, b) in Es and (b, c) in Es and (a, c) in Es
            assert all(len(x) == 1 for x in sel)
        okc = (not Es) or (closed_tri(len(Es), n) == (f.nv, f.ncl))
        assert okc
        rec("tri", truth, okc)

    # ---- 3SUM, AVW14 form ----
    cases = []
    for n in range(1, 10):
        M = n ** 3
        for _ in range(30):
            S = rng.sample(range(-M, M + 1), n) if 2 * M + 1 >= n else list(range(n))
            cases.append(S)
        for _ in range(15):             # small values: many solutions
            S = rng.sample(range(-n - 2, n + 3), n)
            cases.append(S)
        if n >= 3:                      # planted
            for _ in range(15):
                while True:
                    a, b = rng.sample(range(-M // 2, M // 2 + 1), 2)
                    rest = [x for x in rng.sample(range(-M, M + 1), n + 3) if x not in (a, b, a + b)]
                    if a + b not in (a, b) and len(rest) >= n - 3:
                        S = [a, b, a + b] + rest[:n - 3]
                        rng.shuffle(S)
                        break
                cases.append(S)
    cases += [[0, 5, 7], [0, 5, 7, 12], [3, 6, 1], [3, 6, 1, 9], [-2, 0, 2],
              [1, 2, 3], [0, 1, 2, 4], [27, -27, 0], [8, 4, -8, 1]]  # 0 in set; a+a=c traps; extremes
    for S in cases:
        n = len(S)
        if max(abs(x) for x in S) > n ** 3:
            continue
        f, L, decode = build_sum3(S)
        truth = brute_sum3(S)
        T = solve(f)
        assert (T is not None) == truth, S
        if T is not None:
            i, j, kk = decode(T)
            assert len(i) == len(j) == len(kk) == 1
            i, j, kk = i[0], j[0], kk[0]
            assert len({i, j, kk}) == 3 and i < j and S[i] + S[j] == S[kk]
        okc = closed_sum3(n)[:2] == (f.nv, f.ncl)
        assert okc
        rec("sum3", truth, okc)

    # ---- k-SUM, ALW14 form (M = n^(2k)), k = 3, 4, 5, 7 ----
    for k, nmax, reps in ((3, 9, 25), (4, 9, 20), (5, 9, 20), (7, 9, 8)):
        cases = []
        for n in range(1, nmax + 1):
            M = n ** (2 * k)
            for _ in range(reps):
                cases.append([rng.randint(-M, M) for _ in range(n)])
                cases.append([rng.randint(-3, 3) for _ in range(n)])     # many solutions, repeats
            if n >= k:
                for _ in range(reps):                                    # planted
                    while True:
                        sol = [rng.randint(-M // k, M // k) for _ in range(k - 1)]
                        last = -sum(sol)
                        if abs(last) <= M:
                            break
                    xs = sol + [last] + [rng.randint(-M, M) for _ in range(n - k)]
                    rng.shuffle(xs)
                    cases.append(xs)
        # traps: reuse-only solutions, duplicates, extremes
        cases += [[1, -(k - 1)] + [5 ** (j + 3) for j in range(k - 2)],   # 1*(k-1) - (k-1) needs reuse
                  [1] * (k - 1) + [-(k - 1)],                              # duplicates, genuine solution
                  [k ** (2 * k)] * k, [-(k ** (2 * k))] * (k - 1) + [k ** (2 * k)] * 1]
        for xs in cases:
            n = len(xs)
            if max(abs(x) for x in xs) > n ** (2 * k):
                continue
            f, L, decode = build_ksum(xs, k)
            truth = brute_ksum(xs, k)
            T = solve(f)
            assert (T is not None) == truth, (k, xs)
            if T is not None:
                idx = decode(T)
                assert len(idx) == k and all(idx[a] < idx[a + 1] for a in range(k - 1))
                assert sum(xs[i] for i in idx) == 0
            okc = closed_ksum(n, k)[:2] == (f.nv, f.ncl)
            assert okc
            rec("ksum k=%d" % k, truth, okc)

    # ---- k lists, AL13 form, k = 3, 5 ----
    for k, nmax, reps in ((3, 6, 25), (5, 4, 25)):
        for n in range(1, nmax + 1):
            M = max(n ** (2 * k), 4)
            for _ in range(reps):
                if rng.random() < 0.5:
                    lists = [[rng.randint(-4, 4) for _ in range(n)] for _ in range(k)]
                else:
                    lists = [[rng.randint(-M, M) for _ in range(n)] for _ in range(k)]
                    sol = [rng.randint(-M // k, M // k) for _ in range(k - 1)]
                    if abs(sum(sol)) <= M:
                        for j in range(k - 1):
                            lists[j][rng.randrange(n)] = sol[j]
                        lists[k - 1][rng.randrange(n)] = -sum(sol)
                f, L, decode = build_klist(lists, M)
                truth = brute_klist(lists)
                T = solve(f)
                assert (T is not None) == truth, lists
                if T is not None:
                    sel = decode(T)
                    assert all(len(x) >= 1 for x in sel)
                    assert sum(lists[j][sel[j][0]] for j in range(k)) == 0 or \
                        any(sum(lists[j][t[j]] for j in range(k)) == 0 for t in itertools.product(*sel))
                okc = closed_klist(n, k, M)[:2] == (f.nv, f.ncl)
                assert okc
                rec("klist k=%d" % k, truth, okc)

    print("family            instances  satisfiable  closed-form(V,C) matches")
    tot = 0
    for name, (a, b, c) in stats.items():
        print("%-17s %9d %12d %12d" % (name, a, b, c))
        tot += a
    print("total instances", tot, "-- all agree with brute force; every file proper; models decode to valid witnesses")


def run_lengths():
    print("family     size   V          C           N(bits)      N/(n log2^2 n)  bound_ok")
    rng = random.Random(1)
    for m in (2 ** 8, 2 ** 10, 2 ** 12, 2 ** 14, 2 ** 16):
        n = 2 * m                         # worst case n = 2m after dropping isolated vertices
        E = set()
        while len(E) < m:
            u, v = rng.randrange(n), rng.randrange(n)
            if u != v:
                E.add((min(u, v), max(u, v)))
        f, Es, _ = build_tri(n, list(E))
        N = f.nbits()
        dV, dC = len(str(f.nv)), len(str(f.ncl))
        bound = 8 * ((8 + dV + dC) + f.ncl * (3 * dV + 8))
        assert closed_tri(m, n) == (f.nv, f.ncl)
        print("tri    m=%-7d %-10d %-11d %-12d %.2f            %s" %
              (m, f.nv, f.ncl, N, N / (m * math.log2(m) ** 2), N <= bound))
    for k, ns in ((3, (2 ** 8, 2 ** 10, 2 ** 12, 2 ** 14)), (5, (2 ** 8, 2 ** 10, 2 ** 12)),
                  (7, (2 ** 8, 2 ** 10, 2 ** 12))):
        for n in ns:
            if k == 3:
                M = n ** 3
                S = rng.sample(range(-M, M + 1), n)
                f, L, _ = build_sum3(S)
                assert closed_sum3(n)[:2] == (f.nv, f.ncl)
                name = "sum3 "
            else:
                M = n ** (2 * k)
                xs = [rng.randint(-M, M) for _ in range(n)]
                f, L, _ = build_ksum(xs, k)
                assert closed_ksum(n, k)[:2] == (f.nv, f.ncl)
                name = "%dsum " % k
            N = f.nbits()
            dV, dC = len(str(f.nv)), len(str(f.ncl))
            bound = 8 * ((8 + dV + dC) + f.ncl * (3 * dV + 8))
            print("%s  n=%-7d %-10d %-11d %-12d %.2f            %s  (L=%d)" %
                  (name, n, f.nv, f.ncl, N, N / (n * math.log2(n) ** 2), N <= bound, L))


def run_constants():
    """Evaluate the exact upper bound 8[(8+d_V+d_C)+C(3d_V+8)] from the closed forms
    at n = 2^e and 2^e +- 1, 4 <= e <= 40 (finite grid check, not a proof for all n)."""
    def bnd(V, C):
        dV, dC = len(str(V)), len(str(C))
        return 8 * ((8 + dV + dC) + C * (3 * dV + 8))
    print("bound(N)/(n log2^2 n) from closed forms; max over n = 2^e, 2^e+-1, 4 <= e <= 40")
    fams = (("tri(n=2m)", lambda n: closed_tri(n, 2 * n)[:2]),
            ("sum3", lambda n: closed_sum3(n)[:2]),
            ("5sum", lambda n: closed_ksum(n, 5)[:2]),
            ("7sum", lambda n: closed_ksum(n, 7)[:2]))
    for name, fn in fams:
        best, rows = 0, []
        for e in range(4, 41):
            for n in (2 ** e - 1, 2 ** e, 2 ** e + 1):
                V, C = fn(n)
                best = max(best, bnd(V, C) / (n * math.log2(n) ** 2))
            if e in (10, 20, 30, 40):
                V, C = fn(2 ** e)
                rows.append("2^%d:%.1f" % (e, bnd(V, C) / (2 ** e * e * e)))
        print(name, "max=%.1f" % best, " ".join(rows))
    print("dense check: max ratio over every n in [15, 2^18], and the ratio at n = 2")
    for name, fn in fams:
        best, arg = 0, None
        for n in range(15, 2 ** 18 + 1):
            V, C = fn(n)
            r = bnd(V, C) / (n * math.log2(n) ** 2)
            if r > best:
                best, arg = r, n
        V, C = fn(2)
        print(name, "dense max=%.1f at n=%d" % (best, arg), " n=2: %.0f" % (bnd(V, C) / 2.0))
    print("leading constants of the actual length N: sum3 72/log2(10)=%.2f  ksum 16k^2/log2(10): "
          "k=5 %.1f k=7 %.1f  tri 48/log2(10)=%.2f" % (72 / math.log2(10), 16 * 25 / math.log2(10),
                                                      16 * 49 / math.log2(10), 48 / math.log2(10)))


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "check"
    if mode == "check":
        run_checks()
    elif mode == "lengths":
        run_lengths()
    elif mode == "constants":
        run_constants()
    else:
        sys.exit("usage: fine_grained_sat_ladder_reductions.py check|lengths|constants")
