#!/usr/bin/env python3
"""Numbers for notes/a-relativization-barrier-for-the-quasi-linear-square-root-floor.md:
the oracle of notes/a-relativization-barrier-for-the-square-root-floor.md with polylogarithmic padding.
Run: python3 quasi_linear_oracle_scales.py [PARTS]   (default ABCDEFG, about 70 s)

Padding of a wrapper 1.body.1^P:  M = B + |body| + 1,  P = M * g(M),
g(M) = ceil(log2(M+1))^a = bit_length(M)^a,  a >= 1 an integer.
B = |x| + |N| + c_w (t+2) w  (one-bit budget of any branch, as in the earlier note).

Facts used (proved in the note, Sections 1 and 2):
  * a wrapper-format string has >= P+1 one-bits, P is a function of the body,
    and |body| <= M-1;
  * a branch of a wrapper with parameter M holds <= B <= M-2 one-bits, so a
    wrapper-format string it queries has M' g(M') + 1 <= B, i.e.
    M' g(M') <= M - 3.
Scales are indexed by M (not by length):
    ups_0 = 1,  ups_i = (ups_{i-1}+1) g(ups_{i-1}+1) + 2,
class i = wrapper-format strings with M in (ups_{i-1}, ups_i].
    t_i = ups_i (>= any step budget of class i), D_0 = 1,
    W_i = t_i D_{i-1},  p_i = 1/(10 W_i),  sigma_i = ups_i + i + 2,
    D_i = sigma_i - 1,  #class-i strings < 2^{ups_i}.
    Phi_a(B0) = sum_{i<=m} log2(10 W_i) + log2 max(8, 2(B0 D_m + 1)),
    m = least i with ups_i >= Mq(B0) := max{M' : M' g(M') <= B0 - 1}.
Parts:
  A  exhaustive containment check (class of queried string < class of querier)
     and length shrink, small parameters, a = 1, 2, 3.
  B  first scales, exact integers: shrink in M and in length, W_i, -log2 p_i,
     per-scale union bound with the exact body count; total.
  C  Phi_a and the failure threshold x*_a(n) vs sqrt(a n log2 n)/sqrt(2).
  D  upper bound in a cost model: the earlier note's two wrappers per level, merged one
     wrapper per level (fixed s), merged with a variable block schedule;
     consistency check Phi_a(B0_alg) > n.
  E  brute-force exactness of the merged game (Section 6 of the note).
  F  first n meeting the diagonal stage condition for given kappa.
  G  the earlier oracle (padding 4M): merged game with variable blocks, and merging alone.
"""
import math, itertools, random, bisect, sys

LOG2_10 = math.log2(10.0)


def g(M, a):
    return M.bit_length() ** a


# ---------------------------------------------------------------- Part A
def part_A():
    print("Part A: exhaustive containment check, small parameters")
    for a in (1, 2, 3):
        ups = [1]
        while ups[-1] < 10 ** 6:
            u = ups[-1] + 1
            ups.append(u * g(u, a) + 2)

        def cls(M):
            return bisect.bisect_left(ups, M)        # least i with ups_i >= M

        bad_cls = bad_len = cnt = 0
        min_len_ratio = None
        for B in range(0, 400):
            for body in range(1, 120):
                M = B + body + 1
                L = 1 + body + M * g(M, a)
                for Mq in range(2, 400):              # M' = B' + |body'| + 1 >= 2
                    Pq = Mq * g(Mq, a)
                    if Pq + 1 > B:                    # not enough one-bits: cannot be queried
                        break
                    for bq in range(1, Mq):           # |body'| from 1 to M'-1  (B' >= 0)
                        Lq = 1 + bq + Pq
                        cnt += 1
                        if not cls(Mq) < cls(M):
                            bad_cls += 1
                        if not Lq < L:
                            bad_len += 1
                        r = L / Lq
                        if min_len_ratio is None or r < min_len_ratio[0]:
                            min_len_ratio = (r, B, body, Mq, bq)
        print("A a=%d: querier B<400, |body|<120; queried (M',|body'|) exhaustive: cases=%d "
              "class violations=%d length violations=%d; min L/L' = %.3f at (B,|body|,M',|body'|)=%s"
              % (a, cnt, bad_cls, bad_len, min_len_ratio[0], min_len_ratio[1:]))
    print()


# ---------------------------------------------------------------- Part B
def part_B():
    print("Part B: first scales (exact integers); union bound uses #class-i < 2^ups_i")
    for a in (1, 2, 3):
        print("B a=%d" % a)
        print("B   i            ups_i   ups_i/ups_{i-1}  len_i/len_{i-1}   log2 W_i  -log2 p_i   sigma_i  fail_i<=   cum")
        ups_prev, D_prev, cum = 1, 1, 0.0
        len_prev = None
        for i in range(1, 16):
            u = ups_prev + 1
            ups = u * g(u, a) + 2
            # largest length of a class-i wrapper: M = ups, |body| = M-1 (B = 0) gives max length
            Lmax = 1 + (ups - 1) + ups * g(ups, a)
            W = ups * D_prev
            sigma = ups + i + 2
            # exact count of bodies of length <= ups-1 is 2^ups - 2; failure <= count * 2^-sigma
            fail = (2.0 ** (-(i + 2))) * (1 - 2.0 ** (1 - ups)) if ups < 1000 else 2.0 ** (-(i + 2))
            cum += fail
            lr = (Lmax / len_prev) if len_prev else float('nan')
            print("B %3d %16s %14.3f %16.3f %10.2f %10.2f %9s %9.2e %6.4f" % (
                i, (str(ups) if ups < 10 ** 15 else "2^%.2f" % math.log2(ups)),
                ups / ups_prev, lr, math.log2(W), LOG2_10 + math.log2(W),
                (str(sigma) if sigma < 10 ** 15 else "~ups"), fail, cum))
            D_prev = sigma - 1
            ups_prev = ups
            len_prev = Lmax
        print("B a=%d: union bound total over all scales <= sum_i 2^-(i+2) = 1/4" % a)
    print()


# ---------------------------------------------------------------- scale tables
class Scales:
    """log2 ups_i, log2 D_i and cumulative S_m = sum_{i<=m} log2(10 W_i).
    Exact integers while ups < 2^EXACT_BITS, log domain afterwards, rounded up."""
    EXACT_BITS = 3000

    def __init__(self, a, ymax):
        self.a = a
        Y, LD, S = [0.0], [0.0], [0.0]          # index 0: ups_0 = 1, D_0 = 1
        ups, D = 1, 1
        i = 0
        exact = True
        y = 0.0
        while True:
            i += 1
            if exact:
                u = ups + 1
                ups_new = u * g(u, a) + 2
                y_new = self.log2int(ups_new)
                lW = y_new + self.log2int(D)
                D_new = ups_new + i + 1
                lD = self.log2int(D_new)
                ups, D = ups_new, D_new
                if ups_new.bit_length() > self.EXACT_BITS:
                    exact = False
            else:
                # ups_i = (ups+1) bitlen(ups+1)^a + 2 <= ups * bitlen(ups+1)^a * (1 + 2^-2900)
                b = math.floor(y) + 1                   # bit_length(ups+1) (ups+1 < 2^b)
                y_new = y + a * math.log2(b) + 1e-12    # round up
                lW = y_new + LD[-1]
                lD = y_new + 1e-12                      # D_i = ups_i + i + 1, i << ups_i
            Y.append(y_new); LD.append(lD); S.append(S[-1] + LOG2_10 + lW)
            y = y_new
            if y_new > ymax:
                break
        self.Y, self.LD, self.S = Y, LD, S

    @staticmethod
    def log2int(v):
        b = v.bit_length()
        if b <= 1000:
            return math.log2(v)
        return (b - 64) + math.log2(v >> (b - 64))

    def log2Mq(self, x):
        """upper bound on log2 max{M' : M' bitlen(M')^a <= B0 - 1}, B0 = 2^x."""
        a = self.a
        if x < 60:
            B0 = int(math.floor(2.0 ** x))
            lo, hi = 0, max(1, B0)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if mid * g(mid, a) <= B0 - 1:
                    lo = mid
                else:
                    hi = mid - 1
            return math.log2(lo) if lo >= 1 else -1.0
        best = -1.0
        for b in range(int(x) + 2, max(1, int(x - a * math.log2(x) - 10)), -1):
            # M' with bitlen b: 2^{b-1} <= M' <= min(2^b - 1, (B0-1)/b^a)
            cap = x - a * math.log2(b)
            if cap >= b - 1:
                best = min(float(b), cap)
                break
        return best + 1e-12

    def phi(self, x):
        """Phi_a(2^x) and m."""
        lq = self.log2Mq(x)
        if lq < 1.0:                       # no wrapper-format string queryable (M' >= 2)
            m = 0
        else:
            m = bisect.bisect_left(self.Y, lq - 1e-15)
            if m == 0:
                m = 1
        if m >= len(self.Y):               # beyond the table: Phi exceeds S[-1] >> every n used
            return float('inf'), m
        e = x + self.LD[m]
        tail = max(3.0, 1.0 + e + math.log2(1.0 + 2.0 ** (-e)))
        return self.S[m] + tail, m

    def xstar(self, n):
        lo, hi = 0.5, 3.0 * math.sqrt(self.a * n * math.log2(n + 2)) + 60
        for _ in range(120):
            mid = (lo + hi) / 2
            if self.phi(mid)[0] <= n:
                lo = mid
            else:
                hi = mid
        return lo


SCALES = {}


def scales(a, ymax):
    s = SCALES.get(a)
    if s is None or s.Y[-1] < ymax:
        s = Scales(a, ymax)
        SCALES[a] = s
    return s


def part_C(nlist):
    print("Part C: failure threshold x*_a(n) = max log2 B0 with Phi_a(B0) <= n (every machine with log2 B0 <= x* fails)")
    print("C a            n         x*   m(x*)   x*/sqrt(a n log2 n)   x*^2/(a n log2 x*)   Phi monotone")
    for a in (1, 2, 3):
        nmax = max(nlist)
        sc = scales(a, 1.2 * math.sqrt(a * nmax * math.log2(nmax)) + 100)
        mono, prev = True, -1.0
        for k in range(1, 40000):
            v = sc.phi(k * 0.05)[0]
            if v < prev - 1e-9:
                mono = False
            prev = v
        for n in nlist:
            x = sc.xstar(n)
            print("C %d %12d %10.1f %7d %21.4f %20.4f   %s" % (
                a, n, x, sc.phi(x)[1], x / math.sqrt(a * n * math.log2(n)),
                x * x / (a * n * math.log2(x)), mono))
    print("C   (1/sqrt 2 = %.4f)" % (1 / math.sqrt(2)))
    print()


# ---------------------------------------------------------------- Part D
def lse(*xs):
    mx = max(xs)
    return mx + math.log2(sum(2.0 ** (x - mx) for x in xs))


def log2_cost(lX, ltau, a, cw, w, pi=1.0):
    """log2 of the steps to write a wrapper (input X bits, budget tau, width w) and query.
    B = X + cw (tau+2) w; |body| = X + 4w; M = B + |body| + 1; P = M bitlen(M)^a;
    steps = P/w + 3|body|/w + 8."""
    lB = lse(lX, math.log2(cw * w) + lse(ltau, 1.0))
    lbody = lse(lX, math.log2(4 * w))
    lM = lse(lB, lbody, 0.0)
    b = math.floor(lM) + 1
    lP = lM + a * math.log2(b) + math.log2(pi)
    return lse(lP - math.log2(w), math.log2(3) + lbody - math.log2(w), 3.0)


def upper_unmerged(n, a, cw, s, w):
    k = -(-n // s)
    ltD = math.log2(n / w + 2)
    for _ in range(k):
        lt2 = lse(math.log2(s + 4 + n / w), ltD)
        lX2 = lse(math.log2(n + 4 * w), float(s))
        lt1 = lse(1.0 + s - math.log2(w), log2_cost(lX2, lt2, a, cw, w), 0.0)
        ltD = lse(log2_cost(math.log2(n + 4 * w), lt1, a, cw, w), 0.0)
    return ltD + 1e-9, k


def upper_merged(n, a, cw, blocks, w, pi=1.0):
    """blocks = [s_1..s_k] top to bottom.  tau_k = 6 + (n+1)/w;
    tau_i = 4 + 2*2^{s_{i+1}}/w + cost(n + 2^{s_{i+1}}, tau_{i+1}); top T = cost(n, tau_0) + 2."""
    k = len(blocks)
    lt = math.log2(6 + (n + 1) / w)
    for i in range(k - 1, -1, -1):          # E_i calls E_{i+1}, guesses v' of 2^{s_{i+1}} bits
        s = blocks[i]
        lX = lse(math.log2(n), float(s))
        lt = lse(2.0, 1.0 + s - math.log2(w), log2_cost(lX, lt, a, cw, w, pi))
    return lse(log2_cost(math.log2(n), lt, a, cw, w, pi), 1.0)


def variable_blocks(n, a, cw, w, theta):
    """bottom-up: s_{i+1} = floor(log2(theta * w * tau_{i+1}))."""
    lt = math.log2(6 + (n + 1) / w)
    blocks, tot = [], 0
    while tot < n:
        s = max(1, int(math.floor(math.log2(theta * w) + lt)))
        s = min(s, n - tot)
        blocks.append(s)
        tot += s
        lX = lse(math.log2(n), float(s))
        lt = lse(2.0, 1.0 + s - math.log2(w), log2_cost(lX, lt, a, cw, w))
    return list(reversed(blocks))


def best_upper(n, a, cw, mode):
    best = None
    w = 64.0
    for _ in range(4):                      # fixed point w = 2 log2 T
        cand = None
        if mode == "variable":
            for theta in (1 / 64, 1 / 16, 1 / 4, 1, 4):
                bl = variable_blocks(n, a, cw, w, theta)
                v = upper_merged(n, a, cw, bl, w)
                if cand is None or v < cand[0]:
                    cand = (v, max(bl), len(bl))
        else:
            s0 = math.sqrt(a * n * math.log2(n + 2))
            grid = sorted(set(max(1, min(n, int(round(s0 * 2.0 ** (j / 8.0))))) for j in range(-24, 17)))
            for s in grid:
                if mode == "unmerged":
                    v, k = upper_unmerged(n, a, cw, s, w)
                else:
                    k = -(-n // s)
                    v = upper_merged(n, a, cw, [s] * (k - 1) + [n - s * (k - 1)], w)
                if cand is None or v < cand[0]:
                    cand = (v, s, k)
        best = cand
        w = max(16.0, 2.0 * math.ceil(best[0]))
    return best, w


def part_D(nlist):
    print("Part D: relative upper bound in the cost model (log2 T); R5-type consistency Phi_a(B0_alg) > n")
    print("D a cw            n   mode        log2T   s/smax     k   log2T/sqrt(a n log2 n)   log2T/x*   consistent")
    for a in (1, 2):
        for cw in (1,):
            sc = scales(a, 1.2 * math.sqrt(a * max(nlist) * math.log2(max(nlist))) + 100)
            for n in nlist:
                x = sc.xstar(n)
                for mode in ("unmerged", "merged", "variable"):
                    (lT, s, k), w = best_upper(n, a, cw, mode)
                    lB0 = lse(math.log2(n), math.log2(cw * w) + lse(lT, 1.0))
                    ok = sc.phi(lB0)[0] > n
                    print("D %d %2d %12d   %-9s %9.1f %8d %5d %24.4f %10.3f   %s" % (
                        a, cw, n, mode, lT, s, k, lT / math.sqrt(a * n * math.log2(n)), lT / x,
                        "ok" if ok else "CONFLICT"))
    print()


# ---------------------------------------------------------------- Part E
def part_G():
    """The earlier oracle (padding 4M, i.e. a = 0, pi = 4): merged + variable schedule vs its lower threshold."""
    print("Part G: the earlier oracle (P = 4M): merged one-wrapper-per-level game with variable blocks")
    print("G cw            n   log2T(merged,var)  levels  log2T/sqrt(n)   earlier x*(n) (existential_wrapper_oracle_parity_bounds.py)   ratio")
    x11 = {10 ** 6: 1292.4, 10 ** 8: 12950.0}
    for cw in (1,):
        for n in (10 ** 6, 10 ** 8):
            best = None
            w = 64.0
            for _ in range(4):
                cand = None
                for theta in (1 / 64, 1 / 16, 1 / 4, 1, 4):
                    lt = math.log2(6 + (n + 1) / w)
                    blocks, tot = [], 0
                    while tot < n:
                        sb = max(1, int(math.floor(math.log2(theta * w) + lt)))
                        sb = min(sb, n - tot)
                        blocks.append(sb); tot += sb
                        lX = lse(math.log2(n), float(sb))
                        lt = lse(2.0, 1.0 + sb - math.log2(w), log2_cost(lX, lt, 0, cw, w, pi=4.0))
                    lT = lse(log2_cost(math.log2(n), lt, 0, cw, w, pi=4.0), 1.0)
                    if cand is None or lT < cand[0]:
                        cand = (lT, len(blocks))
                best = cand
                w = max(16.0, 2.0 * math.ceil(best[0]))
            print("G %2d %12d %19.1f %7d %14.4f %38.1f %8.3f" % (
                cw, n, best[0], best[1], best[0] / math.sqrt(n), x11[n], best[0] / x11[n]))
            # merging alone: one wrapper per level, fixed block size s (grid around sqrt(n log2(pi c_w)))
            fbest = None
            w = 64.0
            for _ in range(4):
                cand = None
                s0 = math.sqrt(n * math.log2(4.0 * cw))
                for j in range(-24, 17):
                    sb = max(1, min(n, int(round(s0 * 2.0 ** (j / 8.0)))))
                    k = -(-n // sb)
                    v = upper_merged(n, 0, cw, [sb] * (k - 1) + [n - sb * (k - 1)], w, pi=4.0)
                    if cand is None or v < cand[0]:
                        cand = (v, sb, k)
                fbest = cand
                w = max(16.0, 2.0 * math.ceil(fbest[0]))
            print("G %2d %12d   merged, fixed s=%d, k=%d: log2T = %.1f = %.4f sqrt(n); log2T/x* = %.3f" % (
                cw, n, fbest[1], fbest[2], fbest[0], fbest[0] / math.sqrt(n), fbest[0] / x11[n]))
    print("G   asymptotic cost-model value sqrt(2 log2(pi c_w)) = %.4f for pi=4, c_w=1; earlier lower sqrt(log2 3.2) = %.4f"
          % (math.sqrt(2 * math.log2(4)), math.sqrt(math.log2(3.2))))
    print()


def part_E():
    print("Part E: merged game exactness by brute force (every v, every v', every y)")
    rng = random.Random(8)
    for n, sched_list, trials in ((3, ([1, 1, 1], [1, 2], [2, 1], [3]), 30),
                                  (4, ([1, 1, 1, 1], [2, 2], [1, 2, 1], [2, 1, 1]), 20),
                                  (5, ([2, 2, 1], [1, 2, 2], [2, 1, 2]), 8),
                                  (6, ([2, 2, 2],), 4)):
        for sched in sched_list:
            bad_top = bad_sem = cnt = sem_cnt = 0
            k = len(sched)
            pref = [0]
            for s in sched:
                pref.append(pref[-1] + s)
            for _ in range(trials):
                R = [rng.randrange(2) for _ in range(2 ** n)]

                def par(i, rho):          # parity over extensions of rho (length pref[i])
                    rest = n - pref[i]
                    return sum(R[(rho << rest) | z] for z in range(2 ** rest)) % 2

                memo = {}

                def E(i, rho, v):          # i in 1..k: exists y, claim v_y about rho.y false
                    key = (i, rho, v)
                    if key in memo:
                        return memo[key]
                    s = sched[i - 1]
                    res = False
                    if i == k:
                        res = any(R[(rho << s) | y] != v[y] for y in range(2 ** s))
                    else:
                        s2 = sched[i]
                        for y in range(2 ** s):
                            for vp in itertools.product((0, 1), repeat=2 ** s2):
                                if sum(vp) % 2 == 1 - v[y] and not E(i + 1, (rho << s) | y, vp):
                                    res = True
                                    break
                            if res:
                                break
                    memo[key] = res
                    return res

                top = any(sum(v) % 2 == 1 and not E(1, 0, v)
                          for v in itertools.product((0, 1), repeat=2 ** sched[0]))
                cnt += 1
                if top != (sum(R) % 2 == 1):
                    bad_top += 1
                # semantic check of E at every level for every argument
                for i in range(1, k + 1):
                    s = sched[i - 1]
                    for rho in range(2 ** pref[i - 1]):
                        for v in itertools.product((0, 1), repeat=2 ** s):
                            sem = any(par(i, (rho << s) | y) != v[y] for y in range(2 ** s))
                            sem_cnt += 1
                            if E(i, rho, v) != sem:
                                bad_sem += 1
            print("E n=%d blocks=%s: instances=%d top mismatches=%d; E_i(rho,v) checked=%d mismatches=%d"
                  % (n, sched, cnt, bad_top, sem_cnt, bad_sem))
    print()


# ---------------------------------------------------------------- Part F
def part_F():
    print("Part F: least n (geometric search, ratio 1.02) with log2(n+|M|+c_w(2^{kappa sqrt(a n log2 n)}+2) w(n)) < x*_a(n),")
    print("        w(n) = ceil(C (sqrt(a n log2(n+2)) + log2(n+2)))")
    for a in (1, 2):
        sc = scales(a, 1.2 * math.sqrt(a * 1e13 * math.log2(1e13)) + 100)
        for kappa in (0.5, 0.6, 0.65, 0.68):
            for (cw, C, Msz) in ((1, 1, 0), (64, 64, 10 ** 9)):
                n, found = 1000, None
                while n < 10 ** 13:
                    l2T = kappa * math.sqrt(a * n * math.log2(n))
                    wC = math.ceil(C * (math.sqrt(a * n * math.log2(n + 2)) + math.log2(n + 2)))
                    lhs = lse(math.log2(n + Msz), math.log2(cw * wC) + lse(l2T, 1.0))
                    x = sc.xstar(n)
                    if lhs < x:
                        found = (n, round(lhs, 2), round(x, 2))
                        break
                    n = int(n * 1.02) + 1
                print("F a=%d kappa=%.2f c_w=%d C=%d |M|=%d: first n = %s" % (a, kappa, cw, C, Msz, found))
    print()


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "ABCDEFG"
    if "A" in which:
        part_A()
    if "B" in which:
        part_B()
    if "C" in which:
        part_C([10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 10 ** 8, 10 ** 9, 10 ** 10, 10 ** 11, 10 ** 12])
    if "D" in which:
        part_D([10 ** 3, 10 ** 5, 10 ** 7, 10 ** 9])
    if "E" in which:
        part_E()
    if "F" in which:
        part_F()
    if "G" in which:
        part_G()


if __name__ == "__main__":
    main()
