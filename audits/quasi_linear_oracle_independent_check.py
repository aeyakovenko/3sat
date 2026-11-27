#!/usr/bin/env python3
"""Independent check of notes/a-relativization-barrier-for-the-quasi-linear-square-root-floor.md,
written during review without reusing code from quasi_linear_oracle_scales.py.

R1  Fact 0'.2 / containment and both shrink factors, worst case per querier, B up to 2*10^5.
R2  first scales ups_i exactly (Python ints), union-bound sum with the exact body count.
R3  Phi_a and x*_a(n): exact ints while ups < 2^4096, then a 256-bit mantissa; Phi monotone.
R4  merged game: E_i(rho,v) <=> v != true child-parity vector, and the top identity,
    exhaustive over all R for n <= 3, random R for n = 4..6.
R5  cost-model recursion of Part D / Part G re-implemented from the stated formulas.
R6  stage condition of (iv) (Part F) with this file's x*.
"""
import math, sys, bisect, itertools, random

L2_10 = math.log2(10)


def bl(v):
    return v.bit_length()


# ------------------------------------------------------------------ R1
def r1(Bmax=200000):
    print("R1: containment and shrink, worst case per querier budget B (|body|=1, queried M' maximal, |body'|=M'-1)")
    for a in (1, 2, 3):
        ups = [1]
        while ups[-1] < 10 ** 12:
            u = ups[-1] + 1
            ups.append(u * bl(u) ** a + 2)
        cls = lambda M: bisect.bisect_left(ups, M)
        Mq = 1
        worst_len = (float('inf'), None)
        worst_M = (float('inf'), None)
        viol = 0
        for B in range(0, Bmax):
            while (Mq + 1) * bl(Mq + 1) ** a + 1 <= B:
                Mq += 1
            if Mq < 2:
                continue                         # cannot query any wrapper-format string (M' >= 2)
            M = B + 2                            # smallest querier M for this B (|body| = 1)
            if not (cls(Mq) < cls(M)):
                viol += 1
            if not (Mq * bl(Mq) ** a <= M - 3):
                viol += 1
            L = 1 + 1 + M * bl(M) ** a
            Lq = 1 + (Mq - 1) + Mq * bl(Mq) ** a  # longest queryable string
            if not Lq < L:
                viol += 1
            if L / Lq < worst_len[0]:
                worst_len = (L / Lq, (B, Mq))
            if M / Mq < worst_M[0]:
                worst_M = (M / Mq, (B, Mq))
            if L / Lq < 3 ** a / (1 + 2.0 ** -a):
                viol += 1
        print("R1 a=%d B<%d: violations=%d; min L/L' = %.4f at (B,M')=%s; min M/M' = %.4f at %s; proved bound 3^a/(1+2^-a)=%.3f"
              % (a, Bmax, viol, worst_len[0], worst_len[1], worst_M[0], worst_M[1], 3 ** a / (1 + 2.0 ** -a)))
    print()


# ------------------------------------------------------------------ R2
def r2():
    print("R2: first scales, exact")
    for a in (1, 2, 3):
        ups_prev, D_prev = 1, 1
        tot = 0.0
        rows = []
        min_ratio = None
        for i in range(1, 16):
            u = ups_prev + 1
            ups = u * bl(u) ** a + 2
            W = ups * D_prev
            sigma = ups + i + 2
            # exact: (2^ups - 2) * 2^-sigma
            fail = (2 ** ups - 2) / 2 ** sigma if ups < 1000 else 2.0 ** (-(i + 2))
            tot += fail
            r = ups / ups_prev
            min_ratio = r if min_ratio is None else min(min_ratio, r)
            Lmax = ups + ups * bl(ups) ** a       # 1 + (ups-1) + P
            rows.append((i, ups, r, math.log2(W), L2_10 + math.log2(W), sigma, fail, tot))
            ups_prev, D_prev = ups, sigma - 1
        for row in rows[:5]:
            print("R2 a=%d i=%2d ups=%d ratio=%.3f log2W=%.2f -log2p=%.2f sigma=%d fail=%.3e cum=%.4f" % ((a,) + row))
        print("R2 a=%d cum at i=15: %.4f; min ups ratio over i<=15: %.3f" % (a, tot, min_ratio))
    print()


# ------------------------------------------------------------------ R3
class Tab:
    """Y[i] = log2 ups_i, LD[i] = log2 D_i, S[i] = sum_{j<=i} log2(10 W_j)."""
    EXACT = 4096
    MANT = 256

    def __init__(self, a, ymax):
        self.a = a
        Y, LD, S = [0.0], [0.0], [0.0]
        ups, D, i = 1, 1, 0
        while ups.bit_length() <= self.EXACT and Y[-1] <= ymax:
            i += 1
            u = ups + 1
            new = u * bl(u) ** a + 2
            S.append(S[-1] + L2_10 + math.log2(new) + math.log2(D))
            D = new + i + 1
            ups = new
            Y.append(math.log2(ups)); LD.append(math.log2(D))
        # mantissa phase: ups ~ U * 2^e, U has MANT bits (truncated down; relative error < 2^-250 per step)
        e = max(0, ups.bit_length() - self.MANT)
        U = ups >> e
        lD = LD[-1]
        while Y[-1] <= ymax:
            i += 1
            b = U.bit_length() + e              # bitlen(ups + 1) (ups huge, not 2^k - 1 after truncation)
            U = U * b ** a
            sh = max(0, U.bit_length() - self.MANT)
            U >>= sh
            e += sh
            y = math.log2(U) + e
            S.append(S[-1] + L2_10 + y + lD)
            lD = y                              # D_i = ups_i + i + 1, i << ups_i
            Y.append(y); LD.append(lD)
        self.Y, self.LD, self.S = Y, LD, S

    def log2Mq(self, x):
        a = self.a
        if x < 50:
            B0 = int(math.floor(2.0 ** x))
            lo, hi = 0, B0
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if mid * bl(mid) ** a <= B0 - 1:
                    lo = mid
                else:
                    hi = mid - 1
            return math.log2(lo) if lo >= 1 else None, lo
        # largest bit length b with some M' of bit length b: 2^(b-1) * b^a <= B0 - 1
        b = int(x) + 1
        while (b - 1) + a * math.log2(b) > x:
            b -= 1
        return min(math.log2(2.0) * b, x - a * math.log2(b)), None

    def phi(self, x):
        lq, exact = self.log2Mq(x)
        if lq is None or (exact is not None and exact < 2):
            return 3.0, 0                       # no wrapper-format string queryable: m = 0, D_0 = 1
        m = bisect.bisect_left(self.Y, lq - 1e-12)
        if exact is not None:                   # exact comparison for small values
            ups, i = 1, 0
            while ups < exact:
                u = ups + 1
                ups = u * bl(u) ** self.a + 2
                i += 1
            m = i
        m = max(m, 1)
        if m >= len(self.Y):
            return float('inf'), m
        lBD = x + self.LD[m]
        top = max(3.0, 1.0 + lBD + math.log2(1 + 2.0 ** (-lBD)))
        return self.S[m] + top, m

    def xstar(self, n):
        lo, hi = 0.5, 3.0 * math.sqrt(self.a * n * math.log2(n + 2)) + 60
        for _ in range(100):
            mid = (lo + hi) / 2
            if self.phi(mid)[0] <= n:
                lo = mid
            else:
                hi = mid
        return lo


TABS = {}


def tab(a, ymax):
    t = TABS.get(a)
    if t is None or t.Y[-1] < ymax:
        t = Tab(a, ymax)
        TABS[a] = t
    return t


def r3():
    print("R3: x*_a(n) (own implementation)")
    ns = [10 ** k for k in range(3, 13)]
    for a in (1, 2, 3):
        t = tab(a, 1.2 * math.sqrt(a * 1e12 * math.log2(1e12)) + 100)
        mono, prev = True, -1
        for k in range(1, 40001):
            v = t.phi(k * 0.05)[0]
            if v < prev - 1e-9:
                mono = False
            prev = v
        for n in ns:
            x = t.xstar(n)
            print("R3 a=%d n=%14d x*=%11.1f m=%7d x*/sqrt(a n log2 n)=%.4f x*^2/(a n log2 x*)=%.4f" % (
                a, n, x, t.phi(x)[1], x / math.sqrt(a * n * math.log2(n)), x * x / (a * n * math.log2(x))))
        print("R3 a=%d Phi nondecreasing on 0.05..2000: %s" % (a, mono))
    print()


# ------------------------------------------------------------------ R4
def merged_check(n, blocks, R):
    k = len(blocks)
    S = [0]
    for s in blocks:
        S.append(S[-1] + s)

    def par(prefix, plen):                      # parity of R over extensions of prefix (length plen)
        rest = n - plen
        base = prefix << rest
        return sum(R[base:base + (1 << rest)]) & 1

    def truevec(i, rho):                        # rho has length S[i-1]; children have length S[i]
        s = blocks[i - 1]
        return tuple(par((rho << s) | y, S[i]) for y in range(1 << s))

    cache = {}

    def E(i, rho, v):
        key = (i, rho, v)
        if key in cache:
            return cache[key]
        s = blocks[i - 1]
        if i == k:
            res = any(R[(rho << s) | y] != v[y] for y in range(1 << s))
        else:
            s2 = blocks[i]
            res = False
            for y in range(1 << s):
                child = (rho << s) | y
                for vp in itertools.product((0, 1), repeat=1 << s2):
                    if (sum(vp) & 1) == 1 - v[y] and not E(i + 1, child, vp):
                        res = True
                        break
                if res:
                    break
        cache[key] = res
        return res

    bad = 0
    checked = 0
    for i in range(1, k + 1):
        s = blocks[i - 1]
        for rho in range(1 << S[i - 1]):
            tv = truevec(i, rho)
            for v in itertools.product((0, 1), repeat=1 << s):
                checked += 1
                if E(i, rho, v) != (v != tv):
                    bad += 1
    top = any((sum(v) & 1) == 1 and not E(1, 0, v) for v in itertools.product((0, 1), repeat=1 << blocks[0]))
    if top != (sum(R) & 1 == 1):
        bad += 1
    return bad, checked


def compositions(n):
    if n == 0:
        yield []
        return
    for f in range(1, n + 1):
        for rest in compositions(n - f):
            yield [f] + rest


def r4():
    print("R4: merged game, E_i(rho,v) <=> v != true vector; top <=> parity")
    rng = random.Random(20261127)
    for n in (1, 2, 3):
        for blocks in compositions(n):
            if max(blocks) > 3:
                continue
            bad = chk = 0
            for Rint in range(1 << (1 << n)):
                R = [(Rint >> j) & 1 for j in range(1 << n)]
                b, c = merged_check(n, blocks, R)
                bad += b; chk += c
            print("R4 n=%d blocks=%s all %d R: checked=%d mismatches=%d" % (n, blocks, 1 << (1 << n), chk, bad))
    for n, trials in ((4, 40), (5, 6), (6, 2)):
        for blocks in compositions(n):
            if max(blocks) > 2 and not (n == 4 and blocks in ([3, 1], [1, 3])):
                continue
            bad = chk = 0
            for _ in range(trials):
                R = [rng.randrange(2) for _ in range(1 << n)]
                b, c = merged_check(n, blocks, R)
                bad += b; chk += c
            print("R4 n=%d blocks=%s random R x%d: checked=%d mismatches=%d" % (n, blocks, trials, chk, bad))
    print()


# ------------------------------------------------------------------ R5
def lsum(*ls):
    m = max(ls)
    return m + math.log2(sum(2.0 ** (l - m) for l in ls))


def wcost(lX, ltau, a, cw, w, pi):
    """log2 steps to write a wrapper with X input bits and budget tau, then query (model of the note)."""
    lB = lsum(lX, math.log2(cw * w) + lsum(ltau, 1.0))
    lbody = lsum(lX, math.log2(4 * w))
    lM = lsum(lB, lbody, 0.0)
    lP = lM + a * math.log2(math.floor(lM) + 1) + math.log2(pi)
    return lsum(lP - math.log2(w), math.log2(3) + lbody - math.log2(w), 3.0)


def merged_T(n, a, cw, w, pi, blocks):
    lt = math.log2(6 + (n + 1) / w)
    for s in reversed(blocks):
        lt = lsum(2.0, 1.0 + s - math.log2(w), wcost(lsum(math.log2(n), s), lt, a, cw, w, pi))
    return lsum(wcost(math.log2(n), lt, a, cw, w, pi), 1.0)


def variable_sched(n, a, cw, w, pi, theta):
    lt = math.log2(6 + (n + 1) / w)
    out, tot = [], 0
    while tot < n:
        s = max(1, min(n - tot, int(math.floor(math.log2(theta * w) + lt))))
        out.append(s); tot += s
        lt = lsum(2.0, 1.0 + s - math.log2(w), wcost(lsum(math.log2(n), s), lt, a, cw, w, pi))
    return out[::-1]


def best_variable(n, a, cw, pi, thetas):
    w = 64.0
    best = None
    for _ in range(5):
        cand = None
        for th in thetas:
            bl_ = variable_sched(n, a, cw, w, pi, th)
            v = merged_T(n, a, cw, w, pi, bl_)
            if cand is None or v < cand[0]:
                cand = (v, len(bl_), th)
        best = cand
        w = max(16.0, 2.0 * math.ceil(best[0]))
    return best


def best_fixed_merged(n, a, cw, pi):
    w = 64.0
    best = None
    for _ in range(5):
        cand = None
        s0 = math.sqrt(max(a, 1) * n * math.log2(n + 2))
        for j in range(-40, 41):
            s = max(1, min(n, int(round(s0 * 2 ** (j / 16)))))
            k = -(-n // s)
            v = merged_T(n, a, cw, w, pi, [s] * (k - 1) + [n - s * (k - 1)])
            if cand is None or v < cand[0]:
                cand = (v, s, k)
        best = cand
        w = max(16.0, 2.0 * math.ceil(best[0]))
    return best


def r5():
    print("R5: cost model re-implemented (merged game, k+1 nested wrappers)")
    th5 = (1 / 64, 1 / 16, 1 / 4, 1, 4)
    thfine = tuple(2.0 ** (j / 4) for j in range(-32, 13))
    for a, n in ((1, 10 ** 9), (2, 10 ** 9), (1, 10 ** 7)):
        v5 = best_variable(n, a, 1, 1.0, th5)
        vf = best_variable(n, a, 1, 1.0, thfine)
        fm = best_fixed_merged(n, a, 1, 1.0)
        nn = math.sqrt(a * n * math.log2(n))
        print("R5 a=%d n=%d variable(5 thetas): log2T=%.1f ratio=%.4f levels=%d | finer theta grid: %.4f (theta=%.3g) | fixed merged: %.4f"
              % (a, n, v5[0], v5[0] / nn, v5[1], vf[0] / nn, vf[2], fm[0] / nn))
    for n in (10 ** 6, 10 ** 8):
        v5 = best_variable(n, 0, 1, 4.0, th5)
        fm = best_fixed_merged(n, 0, 1, 4.0)
        print("R5 earlier world pi=4 cw=1 n=%d: merged variable log2T=%.1f (%.4f sqrt n), levels=%d; merged fixed %.4f sqrt n"
              % (n, v5[0], v5[0] / math.sqrt(n), v5[1], fm[0] / math.sqrt(n)))
    print()


# ------------------------------------------------------------------ R6
def r6():
    print("R6: stage condition of (iv): least n on the geometric grid (ratio 1.02 from 1000)")
    for a in (1, 2):
        t = tab(a, 1.2 * math.sqrt(a * 1e12 * math.log2(1e12)) + 100)
        for kappa in (0.65, 0.68):
            for cw, C, Msz in ((1, 1, 0), (64, 64, 10 ** 9)):
                n, found = 1000, None
                while n < 10 ** 12:
                    lT = kappa * math.sqrt(a * n * math.log2(n))
                    wC = math.ceil(C * (math.sqrt(a * n * math.log2(n + 2)) + math.log2(n + 2)))
                    lhs = lsum(math.log2(n + Msz), math.log2(cw * wC) + lsum(lT, 1.0))
                    x = t.xstar(n)
                    if lhs < x:
                        found = (n, round(lhs, 2), round(x, 2))
                        break
                    n = int(n * 1.02) + 1
                print("R6 a=%d kappa=%.2f c_w=%d C=%d |M|=%d: %s" % (a, kappa, cw, C, Msz, found))
    print()


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "123456"
    for ch, f in (("1", r1), ("2", r2), ("3", r3), ("4", r4), ("5", r5), ("6", r6)):
        if ch in which:
            f()
            sys.stdout.flush()
