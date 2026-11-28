#!/usr/bin/env python3
# odd_multiplier_bound_independent_arithmetic.py -- independent arithmetic, written during review (exact integers where
# possible), for notes/odd-multiplier-stores-in-a-six-slot-scan.md: thresholds, positivity up to 2^100, the N = 2^80 row,
# and a random grid for C(P) <= 8(|d|+1)h'(R+2)wP^2.
# Writes nothing.  Usage: python3 -B odd_multiplier_bound_independent_arithmetic.py
import math, random
from fractions import Fraction
def flog(b, v):
    k, p = 0, 1
    while p * b <= v:
        p *= b; k += 1
    return k
def R_of(a, w):
    if a == 'lb': return 1
    if a >= 2: return (a + 1) * (flog(a, 2**w - 1) + 1)
    return -a + 1
def wid(N, D=1):  # w = 16 ceil(D log2(N+2)/16), exact via bit length
    # smallest multiple of 16 with 2^w >= (N+2)^D
    w = 16
    while 2**w < (N + 2)**D: w += 16
    return w
def k_of(N, C=32):
    lg = math.log2(N)
    return math.floor(N / (C * lg * lg))
def threshold(a, d=1, hp=16, C=32, D=1):
    # first e (step 0.1) with k > 8(|d|+1)h'(R+2)w, N = floor(2^e)
    for t in range(200, 1000):
        e = t / 10; N = int(2**e)
        w = wid(N, D); k = k_of(N, C); R = R_of(a, w)
        den = 8 * (abs(d) + 1) * hp * (R + 2) * w
        if k > den:
            return e, w, k, R, den
for a in [3, 5, -3, 'lb']:
    print("threshold", a, threshold(a))
# monotonicity after the threshold (does the bound stay positive up to 2^100?)
for a in [3, 5, -3, 'lb']:
    e0 = threshold(a)[0]; bad = []
    for t in range(int(e0 * 10), 1001):
        e = t / 10; N = int(2**e); w = wid(N); k = k_of(N); R = R_of(a, w)
        if k <= 8 * 2 * 16 * (R + 2) * w: bad.append(e)
    print("after threshold, nonpositive at", a, bad[:5])
# N = 2^80, a = 3
N = 2**80; w = wid(N); k = k_of(N); R = R_of(3, w)
P = math.sqrt(k / (8 * 2 * 16 * (R + 2) * w)); T = (P - 1) * (N + 2)
print("N=2^80 a=3: w", w, "k", k, "R", R, "P", P, "T %.4e" % T, "T/(N^1.5/80^2) %.4e" % (T / (N**1.5 / 6400)), "T/(N^1.5/80^1.5) %.4e" % (T / (N**1.5 / 80**1.5)))
# C(P) <= 8(|d|+1)h'(R+2)wP^2: random grid incl. extremes, exact integers
random.seed(5); viol = 0; worst = 0
for _ in range(300000):
    w = random.randint(8, 200); d = random.randint(1, 50); hp = random.randint(1, 100)
    R = random.choice([0, 1, 2, 3, random.randint(0, 2000)]); P = random.choice([1, 2, random.randint(1, 10**6)])
    C = 2*d*P*(3*w+5) + ((2*d+1)*P+1)*hp*(P*(R+1)+1)*(2*w+1) + 2
    B = 8*(d+1)*hp*(R+2)*w*P*P
    worst = max(worst, C / B)
    if C > B: viol += 1
print("C(P) grid (random 300000, w>=8, h'>=1): violations", viol, "max ratio %.4f" % worst)
# where does it first fail in w (h'=1, R=0, P=1, d=1)?
for w in range(1, 10):
    d, hp, R, P = 1, 1, 0, 1
    C = 2*d*P*(3*w+5) + ((2*d+1)*P+1)*hp*(P*(R+1)+1)*(2*w+1) + 2
    B = 8*(d+1)*hp*(R+2)*w*P*P
    print("w", w, "C", C, "B", B, "ok" if C <= B else "FAIL")
