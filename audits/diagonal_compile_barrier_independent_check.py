#!/usr/bin/env python3
"""Independent checks for notes/black-box-routes-through-the-diagonal-compile.md, written during review.

A. Nested opaque gates.  Random 𝔅1-style queries on the Tseitin structure of K4
   (|V| = 4 hidden charges, K = 16 clauses).  Opaque gates are evaluated in
   topological order; each gate's index (computed, 0..K-1) and its 3 argument
   bits are arbitrary functions of the witness y and of the outputs of earlier
   opaque gates.  The reply is f(chi) = OR_y G(y, chi).  Check: the
   1-certificate complexity of f is at most g (= DNF width <= g), which is what
   Theorem BB's adversary needs, also when gates are nested.
   Hashes are of integer tuples, so the output does not depend on PYTHONHASHSEED.

B. General files in 𝔅0.  K clauses, all on the scope (1,2,3), ASCII DIMACS.
   Any 𝔅0 procedure must reference >= K-6 clauses (adversary in the report), so
   its total query length is >= (K-6)*ceil(log2 K).  Print that against M.
"""
import itertools
import math
import random

# ---------------------------------------------------------------- A
EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
NV = 4
INC = [[i for i, e in enumerate(EDGES) if v in e] for v in range(NV)]
PATS = {p: [q for q in itertools.product((0, 1), repeat=3) if sum(q) % 2 == p] for p in (0, 1)}
K = 4 * NV


def forbidden(j, chi):
    v, i = divmod(j, 4)
    return PATS[1 - chi[v]][i]


def opaque(j, args, chi):
    return int(tuple(args) != forbidden(j, chi))


def random_query(rng, g, ybits):
    gates = []
    for k in range(g):
        nin = ybits + k  # y bits plus earlier opaque outputs
        tbl = {}
        gates.append((nin, tbl))
    out_tbl = {}
    return gates, out_tbl


def eval_query(q, rng_seed, y, chi):
    gates, out_tbl = q
    vals = list(y)
    for (nin, tbl) in gates:
        key = tuple(vals[:nin])
        if key not in tbl:
            r = random.Random(hash((rng_seed, len(vals), key)))
            tbl[key] = (r.randrange(K), tuple(r.randint(0, 1) for _ in range(3)))
        j, args = tbl[key]
        vals.append(opaque(j, args, chi))
    key = tuple(vals)
    if key not in out_tbl:
        r = random.Random(hash((rng_seed, -1, key)))
        out_tbl[key] = int(r.random() < 0.15)
    return out_tbl[key]


def cert1(f):
    """max over chi with f=1 of min |S| such that fixing chi on S forces f=1."""
    worst = 0
    for chi, val in f.items():
        if not val:
            continue
        best = None
        for size in range(NV + 1):
            for S in itertools.combinations(range(NV), size):
                if all(f[c] for c in f if all(c[s] == chi[s] for s in S)):
                    best = size
                    break
            if best is not None:
                break
        worst = max(worst, best)
    return worst


def part_a(trials=3000, seed=7):
    rng = random.Random(seed)
    bad = 0
    nonliteral_gate_seen = 0
    for t in range(trials):
        g = rng.randint(1, 3)
        ybits = rng.randint(1, 3)
        q = random_query(rng, g, ybits)
        f = {}
        for chi in itertools.product((0, 1), repeat=NV):
            f[chi] = int(any(eval_query(q, t, y, chi) for y in itertools.product((0, 1), repeat=ybits)))
        c = cert1(f)
        if c > g:
            bad += 1
        if c >= 2:
            nonliteral_gate_seen += 1
    print(f"A: nested opaque gates on K4 Tseitin, trials={trials}: "
          f"1-certificate > g in {bad} queries; queries with certificate width >= 2: {nonliteral_gate_seen}")


# ---------------------------------------------------------------- B
def part_b():
    print("B: 𝔅0, K clauses on scope (1,2,3); bits per clause line '1 2 3 0\\n' + about 1.5 signs")
    print("   K          M(bits)        (K-6)*ceil(log2 K)   ratio to M")
    for e in (10, 14, 18, 22, 26, 30):
        Kc = 1 << e
        M = Kc * 8 * (8 + 1.5) + 8 * len(f"p cnf 3 {Kc}\n")
        cost = (Kc - 6) * math.ceil(math.log2(Kc))
        print(f"   2^{e:2d}  {M:16.0f}  {cost:20d}   {cost / M:8.4f}")
    # the note's example eps = 1/log^2 T: M = T/log2 T; cost/T for this family
    print("   at M = T/log2 T (note's eps = 1/log^2 T):  cost/T for this family")
    for lt in (20, 40, 80):
        T = 2.0 ** lt
        M = T / lt
        Kc = M / (8 * 9.5)
        cost = Kc * math.log2(Kc)
        print(f"   log2 T={lt:3d}: cost/T = {cost / T:.4f}")


if __name__ == "__main__":
    part_a()
    part_b()
