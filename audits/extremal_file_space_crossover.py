#!/usr/bin/env python3
"""Where does k_max(N) > N^(4/5) start to hold for the extremal DIMACS file?
k_max is a step function, so the predicate is not monotone near the threshold:
scan every N in a window, plus a coarse grid on each side.
Written for the-space-route-caps-below-n-to-the-five-fourths.md."""

def min_bytes(k):
    body, d, lo = 0, 1, 1
    while lo <= k:
        hi = min(k, 10**d - 1); body += (hi - lo + 1) * (d + 1); d += 1; lo = 10**(d - 1)
    return len("p cnf ") + len(str(k)) + len(" 1\n") + body + len("0\n")

def kmax(Nbits):
    B = Nbits // 8; lo, hi = 0, B
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if min_bytes(mid) <= B: lo = mid
        else: hi = mid - 1
    return lo

P = lambda N: kmax(N) > N ** 0.8
c = 1431755300
lo, hi = c - 3000, c + 3000
succ = [N for N in range(lo, hi + 1) if P(N)]
fail = [N for N in range(lo, hi + 1) if not P(N)]
print("window [%d, %d]: first success %d, last failure %d" % (lo, hi, succ[0], fail[-1]))
below = [N for N in range(2**20, lo, 997) if P(N)]
above = [N for N in range(hi, 2**33, 1000003) if not P(N)]
print("coarse grid below window (step 997 from 2^20): successes found =", len(below))
print("coarse grid above window (step 1000003 to 2^33): failures found =", len(above))
