#!/usr/bin/env python3
"""Exponent bookkeeping for the space route (exact rationals; logarithmic factors
are tracked separately in
the-space-route-caps-below-n-to-the-five-fourths.md).

Chain: log-word RAM time t  ->  one writable tape time T = O(t^beta polylog)
       ->  space O(T^alpha polylog)  =  O(t^(alpha*beta) polylog).
Premise needed to exclude RAM time N^b:  SAT not in DSPACE(N^(alpha*beta*b) polylog).
Unconditional upper bound: SAT in DSPACE(O(N/log N)) (DIMACS), so the premise is
false whenever alpha*beta*b >= 1: the route's ceiling is b < 1/(alpha*beta).
"""
from fractions import Fraction as F

def table(alpha, beta, label):
    ab = alpha * beta
    print("%s: alpha=%s beta=%s  space exponent per unit RAM time = %s" % (label, alpha, beta, ab))
    for b in [F(1), F(21, 20), F(11, 10), F(6, 5), F(5, 4), F(2), F(3)]:
        a = ab * b
        status = "premise possible (a<1)" if a < 1 else "premise FALSE: SAT in DSPACE(N/log N)"
        print("   exclude RAM time N^%-5s needs SAT notin DSPACE(N^%-6s polylog)  -> %s" % (b, a, status))
    print("   ceiling: b < %s" % (1 / ab))

table(F(2, 5), F(2), "two-fifths preprint (Sep 2026) + direct one-tape scan")
table(F(1, 2), F(2), "classical sqrt(T) one-tape bound (Hopcroft-Ullman/Paterson)")
# what would be needed to reach the quadratic and cubic targets
for target in [F(2), F(3)]:
    print("to reach b=%s with beta=2 need one-tape space exponent alpha < %s" % (target, 1 / (2 * target)))
