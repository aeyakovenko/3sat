#!/usr/bin/env python3
"""Finite checks for the capacity inequalities of
the-instruction-capacity-line-is-capped-at-a-packed-scan.md.

(1) w-bit addition: top sum bit has ANF degree w (so MC >= w-1 by Schnorr's degree bound),
    ripple carry with w-1 ANDs computes every sum bit, and the single equation
    a_{w-2}+b_{w-2}=0 makes the top bit affine (lambda <= 1).
(2) Journal capacities: one addition with even-lane packing and odd-bit XOR readout computes
    IP_{floor(w/2)}; one bitwise AND computes IP_w.
(3) MUX_k: recursive circuit with 2^k-1 ANDs is correct; degree k+1.
Exhaustive over all inputs for the stated widths.
"""
import itertools, sys

def anf_degree(tt, n):
    a = list(tt)
    for i in range(n):
        step = 1 << i
        for x in range(1 << n):
            if x & step:
                a[x] ^= a[x ^ step]
    d = -1
    for x in range(1 << n):
        if a[x]:
            d = max(d, bin(x).count("1"))
    return d

def bits(v, w):
    return [(v >> i) & 1 for i in range(w)]

def check_addition(w):
    n = 2 * w
    top = [0] * (1 << n)
    ok_ripple = True
    ok_flat = True
    flat_size = 0
    for x in range(1 << n):
        a, b = x & ((1 << w) - 1), x >> w
        s = (a + b) & ((1 << w) - 1)
        top[x] = (s >> (w - 1)) & 1
        # ripple carry over F2 with one AND per level: c_{i+1} = (a_i+c_i)(b_i+c_i)+c_i
        A, B = bits(a, w), bits(b, w)
        c, ands, out = 0, 0, []
        for i in range(w):
            out.append(A[i] ^ B[i] ^ c)
            if i < w - 1:
                c = ((A[i] ^ c) & (B[i] ^ c)) ^ c
                ands += 1
        if sum(o << i for i, o in enumerate(out)) != s or ands != w - 1:
            ok_ripple = False
        # flat p_{w-2} = 0  ->  top bit = a_{w-1} + b_{w-1} + a_{w-2}
        if w >= 2 and (A[w - 2] ^ B[w - 2]) == 0:
            flat_size += 1
            if top[x] != (A[w - 1] ^ B[w - 1] ^ A[w - 2]):
                ok_flat = False
    deg = anf_degree(top, n)
    return deg, ok_ripple, ok_flat, flat_size

def check_packed_ip(w):
    m = w // 2
    ok_add = True
    for x in range(1 << (2 * m)):
        xs, ys = bits(x, m), bits(x >> m, m)
        a = sum(xs[j] << (2 * j) for j in range(m))
        b = sum(ys[j] << (2 * j) for j in range(m))
        s = (a + b) & ((1 << w) - 1)
        r = 0
        for j in range(m):
            r ^= (s >> (2 * j + 1)) & 1
        if r != (sum(xs[j] & ys[j] for j in range(m)) & 1):
            ok_add = False
    ok_and = True
    for x in range(1 << (2 * w)):
        u, v = x & ((1 << w) - 1), x >> w
        if bin(u & v).count("1") & 1 != (sum(((u >> j) & 1) & ((v >> j) & 1) for j in range(w)) & 1):
            ok_and = False
    return m, ok_add, ok_and

def mux_circuit(T, idx, k, counter):
    # MUX_k(T, i) = M0 + i_top*(M0+M1), one AND per internal node
    if k == 0:
        return T[0]
    half = 1 << (k - 1)
    m0 = mux_circuit(T[:half], idx, k - 1, counter)
    m1 = mux_circuit(T[half:], idx, k - 1, counter)
    counter[0] += 1
    return m0 ^ (idx[k - 1] & (m0 ^ m1))

def check_mux(k):
    K = 1 << k
    n = K + k
    ok = True
    ands = None
    tt = [0] * (1 << n) if n <= 20 else None
    for x in range(1 << n):
        T = bits(x, K)
        idx = bits(x >> K, k)
        i = sum(b << j for j, b in enumerate(idx))
        cnt = [0]
        val = mux_circuit(T, idx, k, cnt)
        ands = cnt[0]
        if val != T[i]:
            ok = False
        if tt is not None:
            tt[x] = T[i]
    deg = anf_degree(tt, n) if tt is not None and n <= 12 else None
    return ok, ands, deg

if __name__ == "__main__":
    print("== (1) w-bit addition: top sum bit ==")
    for w in range(2, 9):
        deg, okr, okf, fs = check_addition(w)
        print(f"w={w}: degree(top bit)={deg}  => MC>={deg-1}; ripple carry with w-1={w-1} ANDs correct: {okr}; "
              f"top bit affine on flat a_(w-2)+b_(w-2)=0 (|flat|={fs}=2^{2*w-1}): {okf}; floor(w/2)={w//2}")
    print("== (2) journal capacities ==")
    for w in range(2, 9):
        m, oka, okn = check_packed_ip(w)
        print(f"w={w}: one addition computes IP_{m} (m=floor(w/2)): {oka}; one AND computes IP_{w}: {okn}")
    print("== (3) MUX_k ==")
    for k in range(1, 5):
        ok, ands, deg = check_mux(k)
        print(f"k={k}: n={2**k + k}, recursive circuit correct: {ok}, ANDs={ands} (=2^k-1={2**k-1}), degree={deg}")
