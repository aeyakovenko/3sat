#!/usr/bin/env python3
"""Largest number k_max(N) of distinct variables that can occur in a DIMACS CNF
file of at most N bits (8 bits per byte), and the ratio k_max*log2(N)/N.

Lower bound on file length with k distinct occurring variables: the i-th smallest
of k distinct positive integers has at least digits(i) decimal digits, each
occurrence is followed by at least one separator byte, and the file needs a
header "p cnf <n> <m>\n" (n >= largest variable >= k) and a terminating "0\n".
The extremal file is "p cnf k 1\n1 2 ... k 0\n", so the bound is attained.
Written for the-space-route-caps-below-n-to-the-five-fourths.md.
"""
import math, sys

def min_bytes(k):
    # header "p cnf " + digits(k) + " 1\n"  ; body: sum_{i<=k}(digits(i)+1) + "0\n"
    body = 0
    d, lo = 1, 1
    while lo <= k:
        hi = min(k, 10**d - 1)
        body += (hi - lo + 1) * (d + 1)
        d += 1; lo = 10**(d - 1)
    return len("p cnf ") + len(str(k)) + len(" 1\n") + body + len("0\n")

def kmax(Nbits):
    B = Nbits // 8
    lo, hi = 0, B
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if min_bytes(mid) <= B: lo = mid
        else: hi = mid - 1
    return lo

print("%6s %16s %16s %10s %10s" % ("log2N", "N_bits", "k_max", "k*log2N/N", "k/N^0.8"))
for e in range(10, 61, 5):
    N = 2**e
    k = kmax(N)
    print("%6d %16d %16d %10.4f %10.2f" % (e, N, k, k * e / N, k / N**0.8))
# asymptote: k*log10(k) ~ N/8  =>  k*log2(N)/N -> log2(10)/8
print("limit log2(10)/8 = %.4f" % (math.log2(10) / 8))
