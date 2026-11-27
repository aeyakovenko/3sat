#!/usr/bin/env python3
"""The permutation restriction of [AB = C] over F_3, for
the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md.

Claim: pin B to the permutation matrix P with P[h][k] = 1 iff k = pi(h).
Then (AP)[i][k] = A[i][pi^{-1}(k)], so [AP = C] = prod_{i,k} [A[i][pi^{-1}(k)] = C[i][k]].
(a) With all entries in F_3 this is an equality of 3-valued symbols, so on the
    2-bit codes {00,01,10} (11 invalid) it is NOT a product of bit wires.
(b) Pinning the high code bit of every A and C entry to 0 leaves entries in {0,1}
    and the restricted tensor is exactly the product of d^2 bit wires
    A-bit (i,h) -> C-bit (i,pi(h)): r = d^2 routed bits, and for uniform pi each
    A-bit has a uniform destination among q = d positions of its row.
Exhaustive for d = 2, 3 over all permutations.
"""
import itertools, sys
import numpy as np

def check(d):
    perms = list(itertools.permutations(range(d)))
    n = d * d
    # all 0/1 matrices as arrays (2^n, d, d)
    bits = np.array(list(itertools.product((0, 1), repeat=n)), dtype=np.int64).reshape(-1, d, d)
    fails = 0
    checked = 0
    for pi in perms:
        P = np.zeros((d, d), dtype=np.int64)
        for h in range(d):
            P[h, pi[h]] = 1
        AP = np.einsum('aij,jk->aik', bits, P) % 3          # (2^n, d, d)
        # value [AP = C] for every (A, C): compare flattened
        APf = AP.reshape(len(bits), n)
        Cf = bits.reshape(len(bits), n)
        # map 0/1 vectors to integers for fast equality
        w = (1 << np.arange(n)).astype(np.int64)
        apk = APf @ w
        ck = Cf @ w
        val = (apk[:, None] == ck[None, :])                 # [AP = C] over F_3
        # predicted bit-wire product: C[i][pi(h)] = A[i][h]
        pred_key = np.zeros(len(bits), dtype=np.int64)
        for i in range(d):
            for h in range(d):
                pred_key += bits[:, i, h] * (1 << (i * d + pi[h]))
        pred = (pred_key[:, None] == ck[None, :])
        fails += int(np.sum(val != pred))
        checked += val.size
        # each A-bit routed to exactly one C-bit: the accepted (A,C) pairs form a bijection
        assert int(val.sum()) == len(bits)
    # destination distribution of A-bit (0,0) under uniform pi
    dest = {}
    for pi in perms:
        dest[pi[0]] = dest.get(pi[0], 0) + 1
    return checked, fails, dest

def full_f3_not_bitwire(d=1):
    # with entries in F_3 encoded by 2-bit codes, the identity-routing tensor
    # [x = y] on codes has rank 3 (valid codes) instead of 4: not two bit wires
    codes = [(0, 0), (0, 1), (1, 0)]
    M = np.zeros((4, 4), dtype=np.int64)
    for a in range(4):
        for c in range(4):
            ca = (a >> 1, a & 1); cc = (c >> 1, c & 1)
            if ca in codes and cc in codes and ca == cc:
                M[a, c] = 1
    return np.linalg.matrix_rank(M)

if __name__ == '__main__':
    for d in (2, 3):
        checked, fails, dest = check(d)
        print(f"d={d}: (pi,A,C) triples checked={checked} mismatches={fails} "
              f"destination counts of A-bit(0,0) over all pi: {dest}")
    print("rank of one F_3-entry equality on 2-bit codes:", full_f3_not_bitwire(),
          "(a bit-wire pair would have rank 4)")
