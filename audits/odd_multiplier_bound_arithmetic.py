#!/usr/bin/env python3
# odd_multiplier_bound_arithmetic.py -- explicit form of the transfer bound of
# notes/odd-multiplier-stores-in-a-six-slot-scan.md and where it becomes positive.
# Writes nothing.  Usage: python3 -B odd_multiplier_bound_arithmetic.py   (about a second)
# T >= (sqrt(k / (8(|d|+1) h' (R+2) w)) - 1) * (N+2)^D / |d|,  k = floor(N / (C_D log2^2 N)),  w = 16 ceil(D log2(N+2)/16).
# R = proved closed form: a >= 3: (a+1)(floor(log_a(2^w - 1)) + 1); a <= -3: |a| + 1; lookbehind: 1.
# Constants as in the journal's even-multiplier note: d = 1, h' = 16, C_1 = 32.
import math

def ilog(base, v):
    k, p = 0, 1
    while p * base <= v:
        p *= base
        k += 1
    return k

def Rbound(a, w):
    if a == 'lb':
        return 1
    if a >= 2:
        return (a + 1) * (ilog(a, 2 ** w - 1) + 1)
    return -a + 1

def width(N_int, D):
    # least multiple of 16 with 2^w >= (N+2)^D, in exact integer arithmetic
    # (in floating point, 16*ceil(D*log2(N+2)/16) gives w = 80 at N = 2^80, since 2^80 + 2 rounds to 2^80)
    w = 16
    while (1 << w) < (N_int + 2) ** D:
        w += 16
    return w

def bound(N_log2, a, D=1, d=1, hp=16, C=32):
    N = 2.0 ** N_log2
    w = width(int(N), D)  # int(2.0**e) is exact for integer e and an integer bit length near 2^e otherwise
    k = math.floor(N / (C * N_log2 ** 2))
    R = Rbound(a, w)
    P = math.sqrt(k / (8 * (abs(d) + 1) * hp * (R + 2) * w))
    T = (P - 1) * (N + 2) ** D / abs(d)
    return w, k, R, P, T

for a in [3, 5, -3, 'lb']:
    first = None
    for tenth in range(200, 1000):
        e = tenth / 10
        w, k, R, P, T = bound(e, a)
        if T > 0:
            first = (e, w, k, R, P)
            break
    print(f"a={a}: bound first positive at N = 2^{first[0]:.1f} bits (w={first[1]}, k={first[2]}, R<={first[3]}, P_max>={first[4]:.3f})")
    for e in [40, 60, 80]:
        w, k, R, P, T = bound(e, a)
        N = 2.0 ** e
        print(f"   N=2^{e}: w={w} R<={R} P_max>={P:.2f} T>={T:.3e}  T/(N^1.5/log2^2 N)={T / (N ** 1.5 / e ** 2):.3e}  T/(N^1.5/log2^1.5 N)={T / (N ** 1.5 / e ** 1.5):.3e}")

# grid check of C(P) = 2|d|P(3w+5) + ((2|d|+1)P+1) h'(P(R+1)+1)(2w+1) + 2 <= 8(|d|+1) h'(R+2) w P^2  (w >= 8, P >= 1)
viol, cases, worst = 0, 0, 0.0
for w in range(8, 129, 4):
    for d in range(1, 17):
        for hp in [1, 2, 5, 16, 40]:
            for R in [0, 1, 2, 4, 9, 30, 124, 400]:
                for P in [1, 2, 3, 5, 10, 100, 10 ** 4]:
                    C = 2 * d * P * (3 * w + 5) + ((2 * d + 1) * P + 1) * hp * (P * (R + 1) + 1) * (2 * w + 1) + 2
                    B = 8 * (d + 1) * hp * (R + 2) * w * P * P
                    cases += 1
                    worst = max(worst, C / B)
                    if C > B:
                        viol += 1
print(f"grid: C(P) <= 8(|d|+1)h'(R+2)wP^2 on {cases} cases, violations={viol}, max ratio={worst:.4f}")
