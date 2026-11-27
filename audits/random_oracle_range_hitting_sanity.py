#!/usr/bin/env python3
"""Finite sanity checks for Theorems A and B of
range-avoidance-premises-relative-to-a-random-oracle.md.

Monte Carlo at small parameters with a random oracle realized as numpy tables.
These are illustrations at finite size, not proofs.

Part B (one-index premise, universal family U_x(u) = O<2,x,u,1..m>):
  estimate Pr[no index of length n is hit] for several avoiders that spend
  their query budget on their own block and/or on other indices' blocks, and
  compare with
    point-level bound of Theorem B : exp(-2^(n+s-m) * (1 - t/2^s)), t = point queries per run
    seed-level refinement         : exp(-2^(n+s-m) * (1 - k/2^s)), k = seeds touched per run
  (the proof of Theorem B goes through verbatim with tau_j counting touched seeds).

Part A (two-level printer vs a small-memory evaluator):
  one-level printer A1(x) = O<x,1..m>  is reproduced exactly by an evaluator that
  copies x to the query tape; two-level printer A2(x) = O<1, l(x), 1..m> with
  l(x) = O<0,x,1..lam> is hit only when the evaluator's S stored bits plus s seed
  bits pin down l(x).  The evaluator modelled here stores the top S bits of l(x)
  and takes the next s bits from the seed (a specific strategy, not the worst
  case; Theorem A bounds every strategy by m*2^(s+S'-lam) + 2^(s-m)).

Run:  OPENBLAS_NUM_THREADS=1 python3 random_oracle_range_hitting_sanity.py
"""
import math
import numpy as np

rng = np.random.default_rng(20261127)


# ---------------------------------------------------------------- Part B
def part_b(n=10, s=4, m=12, trials=10000, batch=500):
    K, NS, Q = 1 << n, 1 << s, 1 << m
    print(f"Part B: n={n} (K={K} indices), s={s} ({NS} seeds), m={m} ({Q} outputs), "
          f"2^(n+s-m)={2.0**(n+s-m):g}, trials={trials}")
    xs = np.arange(K)
    partner = (xs + 1) % K

    def smallest_not_in(forbidden):
        # forbidden: (B, K, j) int array of values to avoid; return smallest value not among them
        B_, K_, j = forbidden.shape
        cand = np.zeros((B_, K_), dtype=np.int64)
        for _ in range(j + 1):
            clash = (forbidden == cand[..., None]).any(axis=-1)
            cand = np.where(clash, cand + 1, cand)
        return cand

    # each strategy returns A(x) for all x given the table T (B, K, NS) of U_x(u) values
    strategies = {
        "S1 constant 0^m (t=0,k=0)":
            (lambda T: np.zeros(T.shape[:2], dtype=np.int64), 0, 0),
        "S2 learn own seed 0, avoid it (t=m,k=1)":
            (lambda T: smallest_not_in(T[:, :, :1]), m, 1),
        "S3 learn own seed 0 + partner seed 0, avoid both (t=2m,k=2)":
            (lambda T: smallest_not_in(np.concatenate([T[:, :, :1], T[:, partner, :1]], axis=-1)), 2 * m, 2),
        "S4 output partner's seed-0 string (t=m,k=1)":
            (lambda T: T[:, partner, 0], m, 1),
        "S5 learn own seeds 0..3, avoid them (t=4m,k=4)":
            (lambda T: smallest_not_in(T[:, :, :4]), 4 * m, 4),
        "S6 learn partner seeds 0..3, output smallest value avoiding them (t=4m,k=4)":
            (lambda T: smallest_not_in(T[:, partner, :4]), 4 * m, 4),
    }
    E = 2.0 ** (n + s - m)
    for name, (strat, t, k) in strategies.items():
        nohit = 0
        done = 0
        while done < trials:
            b = min(batch, trials - done)
            T = rng.integers(0, Q, size=(b, K, NS), dtype=np.int64)
            A = strat(T)
            hit_x = (T == A[..., None]).any(axis=-1)      # (b, K)
            nohit += int((~hit_x.any(axis=-1)).sum())
            done += b
        p = nohit / trials
        se = math.sqrt(max(p * (1 - p), 1e-12) / trials)
        pt_bound = math.exp(-E * (1 - t / NS)) if t < NS else 1.0
        sd_bound = math.exp(-E * (1 - k / NS))
        flag = "OK" if p <= sd_bound + 3 * se else "VIOLATION"
        print(f"  {name:72s} Pr[no hit]~{p:.4f} (+-{se:.4f})  seed-bound {sd_bound:.4f}  "
              f"point-bound {pt_bound:.4f}  {flag}")
    # closed forms for strategies whose per-index events are independent
    print(f"  exact S1 = (1-2^-m)^(2^s*2^n)     = {(1 - 1/Q)**(NS*K):.4f}")
    print(f"  exact S2 = (1-2^-m)^((2^s-1)*2^n) = {(1 - 1/Q)**((NS-1)*K):.4f}")
    print(f"  exact S5 = (1-2^-m)^((2^s-4)*2^n) = {(1 - 1/Q)**((NS-4)*K):.4f}")


# ---------------------------------------------------------------- Part A
def part_a(n=12, m=16, s=3, S=3, lams=(4, 6, 8, 10, 12, 14), trials=20):
    K = 1 << n
    print(f"Part A: n={n} ({K} indices), m={m}, seed s={s}, stored label bits S={S}, trials={trials}")
    # one-level printer: evaluator copies x onto the query tape -> reproduces A1(x) exactly
    hits1 = []
    for _ in range(trials):
        T1 = rng.integers(0, 1 << m, size=K, dtype=np.int64)   # O<x,1..m> packed
        A1 = T1
        E1 = T1[np.arange(K)]                                   # evaluator's query <x,i>
        hits1.append(float((A1 == E1).mean()))
    print(f"  one-level printer, copy-x evaluator: mean hit fraction {np.mean(hits1):.4f}")
    for lam in lams:
        hf = []
        for _ in range(trials):
            L = rng.integers(0, 1 << lam, size=K, dtype=np.int64)        # l(x) = O<0,x,1..lam>
            T2 = rng.integers(0, 1 << m, size=1 << lam, dtype=np.int64)  # O<1,l,1..m>
            A2 = T2[L]
            keep = min(S, lam)
            seedbits = min(s, lam - keep)
            rest = lam - keep - seedbits
            top = (L >> (lam - keep)) << (lam - keep)                    # stored S bits of l(x)
            us = np.arange(1 << seedbits, dtype=np.int64)
            G = top[:, None] | (us[None, :] << rest)                      # guessed labels, one per seed
            R = T2[G]                                                     # evaluator outputs per seed
            hf.append(float((R == A2[:, None]).any(axis=1).mean()))
        bound = min(1.0, m * 2.0 ** (s + S - lam) + 2.0 ** (s - m))
        heur = min(1.0, 2.0 ** (S + s - lam) + 2.0 ** (s - m))
        print(f"  two-level printer, lam={lam:2d}: mean hit fraction {np.mean(hf):.4f}   "
              f"heuristic 2^(S+s-lam)+2^(s-m) = {heur:.4f}   Theorem-A-style bound m*2^(s+S-lam)+2^(s-m) = {bound:.4f}")


if __name__ == "__main__":
    part_b()
    print()
    part_a()
