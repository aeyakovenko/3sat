#!/usr/bin/env python3
"""Exponent bookkeeping for RAM time in two-thirds-power space and the QBF chain lemma.

Chain: QBF in DTIME_RAM(N^c), RAM time t in space t^alpha polylog, DSPACE(S)
compiles to QDIMACS of S^beta polylog bits  ==>  c*alpha*beta >= 1.
So the route excludes QBF time N^c exactly for c < 1/(alpha*beta); it says
something non-trivial only when 1/(alpha*beta) > 1.
"""
from fractions import Fraction as F

print("== chain bound: QBF not in DTIME_RAM(N^c) for c < 1/(alpha*beta) ==")
rows = [
    ("RAM via one-tape scan + two-fifths (space-route note)", F(4, 5), F(2)),
    ("RAM, direct instantiation of the two-fifths method (Claim R)", F(2, 3), F(2)),
    ("multitape TM, Williams 2025 (sqrt(t log t))", F(1, 2), F(2)),
    ("one-writable-tape TM, two-fifths theorem", F(2, 5), F(2)),
    ("hypothetical RAM alpha = 2/5", F(2, 5), F(2)),
]
for name, a, b in rows:
    c = 1 / (a * b)
    tag = "non-trivial (superlinear)" if c > 1 else "vacuous (c <= 1)"
    print(f"  alpha={str(a):>4} beta={str(b):>2}  excludes c < {str(c):>4} = {float(c):.3f}   {tag}   [{name}]")

print("== what is needed for a superlinear bound: alpha*beta < 1 ==")
for a in (F(4, 5), F(2, 3), F(1, 2)):
    print(f"  alpha={a}: need beta < {1/a} (Savitch gives 2)")
for b in (F(2), F(3, 2)):
    print(f"  beta={b}: need alpha < {1/b}")

print("== RAM balance: space(k) = k^2 + t/k (word ~ L = k^2 visits, stack ~ E*k, E = t/k^2) ==")
for e in (12, 24, 48, 96):
    t = 2 ** e
    # integer minimisation over k
    import math
    # k ranges over 2^(x/16); f(k) = k^2 + t/k is convex in log k
    best = min(((2 ** (x / 16)) ** 2 + t / 2 ** (x / 16), 2 ** (x / 16)) for x in range(0, 16 * (e // 2 + 2)))
    print(f"  t=2^{e:<3} best k=2^{math.log2(best[1]):.2f}  log_t(space)={math.log(best[0], t):.4f}")
print("  limit exponent 2/3")

print("== one-tape balance (preprint): k^2 + (T/k^4)*k, exponent -> 2/5 ==")
import math
for e in (20, 40, 80):
    T = 2 ** e
    best = min(((2 ** (x / 16)) ** 2 + T / (2 ** (x / 16)) ** 3, x) for x in range(0, 16 * (e // 2 + 2)))
    print(f"  T=2^{e:<3} log_T(space)={math.log(best[0], T):.4f}")

print("== sanity flag: single-head d-dimensional tapes ==")
print("  factored method with cube blocks of side s: space s^d + k^2 + T/(s k)  ->  T^(2d/(3d+2))")
print("  Williams 2025 Thm (d-dim multitape): (T log T)^(1-1/(d+1))")
for d in range(1, 7):
    fm = F(2 * d, 3 * d + 2)
    wi = 1 - F(1, d + 1)
    print(f"  d={d}: factored(single head)={str(fm):>5}={float(fm):.3f}   RAM-instantiation=2/3   Williams={str(wi):>4}={float(wi):.3f}")
