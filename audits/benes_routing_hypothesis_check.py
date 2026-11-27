#!/usr/bin/env python3
"""For the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md:
the routing hypothesis of the uniform-destinations lemma is
met by a fixed topology of size O(r log r), so that lemma can never certify more.

Part A: a 2x2 switch as a FIXED trivalent topology whose vertex tables are chosen
per setting.  Topology: three controlled-XOR stages u<-u+v, v<-u+v, u<-u+v, each
stage = one copy vertex (arity 3) + one 'XOR-or-pass' vertex (arity 3).  With the
XOR tables we get SWAP; with 'pass' tables (output = first input) we get identity.
We contract the 4-leg tensor over the integers (all entries 0/1, so the result is
the same in every field) and compare with the identity / swap wire tensors.

Part B: the Benes topology on r = 2^k terminals (2k-1 stages of r/2 switches)
realizes every permutation for some setting.  Exhaustive over all settings for
r = 4 (6 switches) and r = 8 (20 switches, 2^20 settings).
Size: (2k-1)(r/2) switches * 6 trivalent vertices = O(r log r).
"""
import itertools, math, sys
import numpy as np

# ---------- Part A: switch gadget ----------
def copy3():
    T = np.zeros((2, 2, 2), dtype=np.int64)
    T[0, 0, 0] = T[1, 1, 1] = 1
    return T

def xor3():      # T[a, b, out] = [out = a xor b]
    T = np.zeros((2, 2, 2), dtype=np.int64)
    for a in range(2):
        for b in range(2):
            T[a, b, a ^ b] = 1
    return T

def pass3():     # T[a, b, out] = [out = a], b ignored
    T = np.zeros((2, 2, 2), dtype=np.int64)
    for a in range(2):
        for b in range(2):
            T[a, b, a] = 1
    return T

def stage(target_first, gate):
    """One controlled stage on wires (u, v): copy the control, combine with target.
    Returns 4-leg tensor S[u_in, v_in, u_out, v_out]."""
    C = copy3(); G = gate
    S = np.zeros((2, 2, 2, 2), dtype=np.int64)
    for u in range(2):
        for v in range(2):
            for uo in range(2):
                for vo in range(2):
                    tot = 0
                    for c1 in range(2):      # internal wires: two copies of control
                        for c2 in range(2):
                            if target_first:  # u <- u (+) v : control v copied
                                tot += C[v, c1, c2] * G[u, c1, uo] * (1 if c2 == vo else 0)
                            else:             # v <- u (+) v : control u copied
                                tot += C[u, c1, c2] * G[v, c1, vo] * (1 if c2 == uo else 0)
                    S[u, v, uo, vo] = tot
    return S

def compose(S1, S2):
    return np.einsum('abcd,cdef->abef', S1, S2)

def switch(setting):
    g = xor3() if setting else pass3()
    return compose(compose(stage(True, g), stage(False, g)), stage(True, g))

ID = np.zeros((2, 2, 2, 2), dtype=np.int64)
SW = np.zeros((2, 2, 2, 2), dtype=np.int64)
for u in range(2):
    for v in range(2):
        ID[u, v, u, v] = 1
        SW[u, v, v, u] = 1

# ---------- Part B: Benes coverage ----------
def benes(k):
    """Return list of stages; each stage is (list of switch pairs) followed by a
    fixed wiring permutation.  Recursive construction on positions 0..r-1."""
    r = 1 << k
    if k == 1:
        return [[(0, 1)]], [list(range(2))]
    # first stage: switches on (2i, 2i+1); then outputs 2i -> top i, 2i+1 -> bottom i
    sub_st, sub_w = benes(k - 1)
    half = r // 2
    stages = [[(2 * i, 2 * i + 1) for i in range(half)]]
    wires = [[(p // 2) if p % 2 == 0 else half + p // 2 for p in range(r)]]
    for st, w in zip(sub_st, sub_w):
        stages.append([(a, b) for (a, b) in st] + [(a + half, b + half) for (a, b) in st])
        wires.append([w[p] if p < half else half + w[p - half] for p in range(r)])
    # last stage: inverse shuffle then switches on (2i, 2i+1)
    inv = [0] * r
    for p in range(r):
        inv[wires[0][p]] = p
    wires[-1] = [inv[wires[-1][p]] for p in range(r)]
    stages.append([(2 * i, 2 * i + 1) for i in range(half)])
    wires.append(list(range(r)))
    return stages, wires

def realized(stages, wires, setting_bits, r):
    pos = list(range(r))          # pos[token] = current position
    where = list(range(r))        # where[position] = token
    idx = 0
    for st, w in zip(stages, wires):
        for (a, b) in st:
            if (setting_bits >> idx) & 1:
                where[a], where[b] = where[b], where[a]
            idx += 1
        nw = [0] * r
        for p in range(r):
            nw[w[p]] = where[p]
        where = nw
    out = [0] * r
    for p in range(r):
        out[where[p]] = p          # token -> final position
    return tuple(out)

if __name__ == '__main__':
    print("switch gadget: pass tables give identity:", np.array_equal(switch(0), ID),
          "| XOR tables give swap:", np.array_equal(switch(1), SW))
    for k in (2, 3):
        r = 1 << k
        stages, wires = benes(k)
        nsw = sum(len(s) for s in stages)
        seen = set()
        for s in range(1 << nsw):
            seen.add(realized(stages, wires, s, r))
        print(f"r={r}: stages={len(stages)} switches={nsw} "
              f"trivalent vertices={6*nsw} permutations realized={len(seen)} of {math.factorial(r)}")
