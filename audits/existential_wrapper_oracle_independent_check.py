#!/usr/bin/env python3
"""Independent re-derivation of the numbers of
notes/a-relativization-barrier-for-the-square-root-floor.md,
written during review independently of existential_wrapper_oracle_parity_bounds.py.
Run: python3 existential_wrapper_oracle_independent_check.py

R1  Phi(B0) with lambda_i = (pi+1) rho^i, D_i = floor(lambda_i)+i+2 (floor taken
    exactly with rationals while lambda_i < 2^75, after which it changes log2 by
    < 1e-20), W_i = (lambda_i/pi) D_{i-1}, p_i = 1/(10 W_i), q = B0,
    tail = log2 max(8, 2(q D_m + 1)).  x*(n) = sup log2 B0 with Phi(B0) <= n.
R2  Union-bound and Chernoff bookkeeping.
R3  Asymptotics: sqrt(n log2 rho) - x*(n) up to n = 1e12 (is the deficit bounded?).
R4  Stage condition of (iv): least n with
    log2(n + |M| + c(2^{1.29 sqrt n}+2) w_C(n)) < x*(n), for a few (c, C, |M|).
R5  Consistency: the (ii) algorithm must NOT be excluded by (iii).
R6  Fact 0 arithmetic on a grid.
"""
import math, bisect
from fractions import Fraction as F

TABLES = {}

def tables(pi, mmax):
    key = (pi, mmax)
    if key in TABLES:
        return TABLES[key]
    piF = F(pi)
    rho = piF * piF / (piF + 1)
    lam = piF + 1
    log2rho = math.log2(pi * pi / (pi + 1))
    log2lam0 = math.log2(pi + 1)
    L2lam, L2D, S = [log2lam0], [0.0], [0.0]     # index 0: lambda_0, D_0 = 1
    for i in range(1, mmax + 1):
        if i <= 45:
            lam = lam * rho
            l2lam = math.log2(lam.numerator) - math.log2(lam.denominator)
            D = math.floor(lam) + i + 2
            l2D = math.log2(D)
        else:
            l2lam = log2lam0 + i * log2rho
            l2D = l2lam                       # floor(lam)+i+2 = lam (1 + O(i/lam)), lam > 2^75
        l2W = l2lam - math.log2(pi) + L2D[i - 1]
        S.append(S[-1] + math.log2(10) + l2W)
        L2lam.append(l2lam)
        L2D.append(l2D)
    TABLES[key] = (L2lam, L2D, S)
    return TABLES[key]

def phi(log2B0, pi=4, mmax=1100000):
    L2lam, L2D, S = tables(pi, mmax)
    top = math.log2((pi + 1) / pi) + log2B0
    m = bisect.bisect_left(L2lam, top, lo=1)      # least i >= 1 with log2 lambda_i >= top
    assert m <= mmax
    e = log2B0 + L2D[m]
    tail = max(3.0, 1.0 + e + math.log2(1.0 + 2.0 ** (-e)))
    return S[m] + tail, m

def xstar(n, pi=4):
    lo, hi = 0.0, (math.sqrt(math.log2(pi * pi / (pi + 1))) + 0.5) * math.sqrt(n) + 60
    for _ in range(200):
        mid = (lo + hi) / 2
        if phi(mid, pi)[0] <= n:
            lo = mid
        else:
            hi = mid
    return lo

def main():
    print("R1/R3: x*(n) vs sqrt(n log2 rho)")
    print("  pi             n        x*(n)  sqrt(n log2 rho)   deficit      m   x*/sqrt(n)")
    for pi in (4, 16):
        rho = pi * pi / (pi + 1)
        for n in (10**3, 10**4, 10**5, 10**6, 10**7, 10**8, 10**9, 10**10, 10**11, 10**12):
            x = xstar(n, pi)
            s = math.sqrt(n * math.log2(rho))
            print("  %2d %13d %12.2f %16.2f %9.2f %6d %11.5f" % (pi, n, x, s, s - x, phi(x, pi)[1], x / math.sqrt(n)))
    mono, prev = True, -1.0
    for k in range(1, 200000):
        v = phi(k * 0.05)[0]
        if v < prev - 1e-9:
            mono = False
        prev = v
    print("  Phi nondecreasing on log2 B0 = 0.05..10000 step 0.05:", mono)
    print()
    print("R2: union bound and final margin")
    piF = F(4); rho = piF * piF / (piF + 1); lam = piF + 1; tot = F(0)
    for i in range(1, 120):
        lam *= rho
        sigma = math.floor(lam) + i + 3
        tot += F(2) ** (math.floor(lam) + 1 - sigma)
    print("  sum_i 2^{floor(lam_i)+1} 2^{-sigma_i} (i<120) =", float(tot), "  1 - 1/4 - e^-1 =", round(1 - 0.25 - math.exp(-1), 4))
    print()
    print("R4: least n (geometric search, ratio 1.02) meeting the stage condition of (iv)")
    for (c, C, M) in ((1, 1, 0), (2, 4, 10**4), (8, 16, 10**6), (64, 64, 10**9)):
        n, found = 10**4, None
        while n < 10**13:
            l2T = 1.29 * math.sqrt(n)
            wC = math.ceil(C * (math.sqrt(n) + math.log2(n + 2)))
            lhs = l2T + math.log2(c * wC) + math.log2(1 + (n + M + 2 * c * wC) * 2.0 ** (-l2T) / (c * wC))
            x = xstar(n)
            if lhs < x:
                found = (n, round(lhs, 2), round(x, 2))
                break
            n = int(n * 1.02) + 1
        print("  c=%d C=%d |M|=%d: first n = %s" % (c, C, M, found))
    print()
    print("R5: the (ii) algorithm is not excluded by (iii): need Phi(B0_alg) > n")
    for (pi, c) in ((4, 1), (4, 2), (16, 1)):
        for n in (10**3, 10**4, 10**5, 10**6, 10**8):
            K = (pi * c) ** 2
            best = None
            for s in range(1, int(6 * math.sqrt(n * math.log2(K))) + 20):
                k = -(-n // s)
                lt = k * math.log2(K) + s
                if best is None or lt < best[0]:
                    best = (lt, s, k)
            lt = best[0]
            l2B0 = lt + math.log2(c * 2 * lt)
            lt_var = 2 * math.sqrt(n * math.log2(pi * c))      # variable-block schedule (estimate)
            l2B0v = lt_var + math.log2(c * 2 * lt_var)
            p1, p2 = phi(l2B0, pi)[0], phi(l2B0v, pi)[0]
            print("  pi=%2d c=%d n=%10d  uniform: log2B0=%9.1f Phi=%13.1f %s | variable: log2B0=%9.1f Phi=%13.1f %s" % (
                pi, c, n, l2B0, p1, "ok" if p1 > n else "CONFLICT", l2B0v, p2, "ok" if p2 > n else "CONFLICT"))
    print()
    print("R6: Fact 0 arithmetic (pi=4): P >= pi j/(pi+1), B < L/pi, max queried wrapper length < L/rho")
    pi = 4; bad = 0; cnt = 0
    for B in range(0, 2000, 3):
        for body in range(1, 600, 7):
            P = pi * (B + body + 1); L = 1 + body + P; cnt += 1
            if P * (pi + 1) < pi * L: bad += 1
            if B * pi >= L: bad += 1
            jmax = (pi + 1) * B // pi                 # wrapper-format length j needs >= pi j/(pi+1) ones <= B
            if jmax * pi * pi >= (pi + 1) * L: bad += 1
    print("  cases=%d violations=%d" % (cnt, bad))

if __name__ == "__main__":
    main()
