#!/usr/bin/env python3
"""Per-cut advice total (Corollary 6 of the seed note, summed over the phase-2 cuts y <= m/2)
against the one shared landmark bank, for h = g = ceil(m^(1/3)).

Two conventions for Q.  Qd = h: values of f used per decoded word (the note's D2
convention); the landmark decoder uses at most h (proved; checked exhaustively at m <= 8).
Qb = W*h: the note's Corollary 6 convention Q = C0*E*w'*K_d with C0 = 1, E = h field probes
per bit call, w' = W = bit length of m+1 bit calls per word, K_0 = 1.  The per-cut
total uses Corollary 6 part 2 (all but an m*2^(1-t) fraction of permutations need more than
t = floor(m/(4(Q+1))) bits at EVERY phase-2 head y <= m/2 simultaneously), so the per-cut
total is floor(m/(2g)) * t on those permutations.  (Part 1's exact-binomial s_min is a
one-cut, worst-permutation bound and is printed only for reference; it is not summed.)  The shared bank is
6 + wb(3 + 2K) bits with K <= floor(2m/h) - (bound) ; we print the bound K = 2m/h and,
for m <= 2^20, the K of one random permutation.
"""
import math, random
from math import lgamma, log

def log2C(n, k):
    if k < 0 or k > n:
        return float('-inf')
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / log(2)

def s_min(m, Q):
    best = 0.0
    for t in range(1, m // 2 + 1):
        if t * (Q + 1) > m:
            break
        best = max(best, log2C(m, t) - log2C(t * (Q + 1), t) - 1)
    return best

def cbrt_ceil(m):
    h = 1
    while h ** 3 < m:
        h += 1
    return h

def marks(f, h):
    m = len(f); seen = [False] * m; K = 0
    for s in range(m):
        if seen[s]: continue
        l = 0; x = s
        while not seen[x]:
            seen[x] = True; x = f[x]; l += 1
        if l > h: K += -(-l // h)
    return K

rng = random.Random(7)
print(" log2m        m   h=g    Qd     t/cut  cuts(y<=m/2)  per-cut total   bank(K=2m/h)  bank(random f)  ratio  except.frac | Qb   total(Qb)  ratio(Qb)")
for e in range(6, 27, 2):
    m = 1 << e
    h = g = cbrt_ceil(m)
    Q = h
    s = m // (4 * (Q + 1))                 # Corollary 6 part 2, simultaneous at all heads
    Qb = (m + 1).bit_length() * h
    sb = m // (4 * (Qb + 1))
    frac = m * 2.0 ** (1 - s)               # exceptional fraction of permutations
    cuts = m // (2 * g)
    total = cuts * s
    wb = max(m, g, h, 2 * m // h).bit_length()
    bank_bound = 6 + wb * (3 + 2 * (2 * m // h))
    if m <= 1 << 20:
        f = list(range(m)); rng.shuffle(f); K = marks(f, h)
        bank_rand = 6 + wb * (3 + 2 * K)
    else:
        bank_rand = float('nan')
    print(f"{e:5d} {m:9d} {h:5d} {Q:5d} {s:11.1f} {cuts:12d} {total:14.0f} {bank_bound:14d} {bank_rand:15} {total/bank_bound:8.3f} {min(frac,1.0):9.2e} | {Qb:5d} {m//(2*g)*sb:10.0f} {m//(2*g)*sb/bank_bound:8.3f}")

# Fraction of N occupied by the whole inverse table, log2(m!)/N, main family.
for m in (4096, 32768):
    D = len(str(m + 3))
    N = 8 * (8 + D + len(str(2 * m + 7)) + (2 * m + 7) * (3 * D + 8))
    print(f"m={m}: N={N} bits, log2(m!)/N = {lgamma(m + 1) / log(2) / N:.4f}")
