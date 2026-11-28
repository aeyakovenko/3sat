"""Node game of the round-three truth-claim entry on abstract RAM runs, exact values. It generalises the
last-writer game of node_game_with_range_challenges.py (the round-two QBF entry).

Run model: steps 1..T, each a tuple (kind, addr, pub):
  kind 'S' store, 'L' load, 'X' load-then-store at the same address (overwrite ladder);
  pub True if the step's kind and address are fixed by the program text (no data dependence).
Nodes 0..T: node u = machine state after step u; node 0 is known.
For a loading step i with last writer p(i) (0 if none):
  hard(i) = {i-1} + {p(i)} (if p(i) >= 1 and p(i) != i-1); store-only steps have hard(i) = {i-1}.
  R(i) = {k-1 : p(i) < k < i, k-1 >= 1, step k challengeable}; "challengeable" means: if PUB is off,
  every step (the round-two convention); if PUB is on, only steps that write at a data-dependent address
  (kind 'S' or 'X' with pub False; data-dependent kinds are not modelled, every kind is public here).
Game (Dymond-Tompa with the round-two range challenge), state (c, P, b), b = challenger's remaining word moves:
  place v not in P: cost 1 + max(V(v,P+v,b), V(c,P+v,b));
  if hard(c) <= P, declare ready: challenger accepts (0) or, if b > 0, names u in R(c) (one word):
    u in P -> 0; else the prover places u (cost 1 to the prover, plus `cc` to the path) and the
    challenge moves to u: 1 + cc + V(u, P+u, b-1).
  Rule P: cc = 0 and b = infinity (= T).  V(b) curve: cc = 0, b = 0..T.  Sum rule: cc = 1, b = T.
Usage: python3 -I -B truth_claim_node_game.py [Tmax, default 12]   (values on the round-three instance families, T = 2..Tmax)
       python3 -I -B truth_claim_node_game.py --regress   (reproduces node_game_with_range_challenges.py's table)
"""
import sys, random
from functools import lru_cache

def last_writer_structure(steps, pub_switch):
    T = len(steps)
    last = {}
    hard = [[]]
    R = [[]]
    for i in range(1, T + 1):
        kind, a, pub = steps[i - 1]
        if kind in ('L', 'X'):
            p = last.get(a, 0)
            h = [i - 1] + ([p] if p >= 1 and p != i - 1 else [])
            rng = []
            for k in range(p + 1, i):
                if k - 1 < 1:
                    continue
                kk, ka, kp = steps[k - 1]
                if pub_switch:
                    if kk in ('S', 'X') and not kp:
                        rng.append(k - 1)
                else:
                    rng.append(k - 1)
            hard.append(h); R.append(rng)
        else:
            hard.append([i - 1]); R.append([])
        if kind in ('S', 'X'):
            last[a] = i
    return hard, R

def make_solver(T, hard, R, cc):
    full = (1 << (T + 1)) - 1
    hardmask = [0] * (T + 1)
    for i in range(1, T + 1):
        for h in hard[i]:
            hardmask[i] |= 1 << h
    sys.setrecursionlimit(1000000)

    @lru_cache(maxsize=None)
    def V(c, P, b):
        best = None
        if hardmask[c] & ~P == 0:
            val = 0
            if b > 0:
                for u in R[c]:
                    if not (P >> u) & 1:
                        val = max(val, 1 + cc + V(u, P | (1 << u), b - 1))
            best = val
            if best == 0:
                return 0
        free = full & ~P
        v = 1
        while free >> v:
            if (free >> v) & 1:
                Q = P | (1 << v)
                x = V(v, Q, b)
                if best is None or 1 + x < best:
                    y = V(c, Q, b)
                    val = 1 + max(x, y)
                    if best is None or val < best:
                        best = val
            v += 1
        return best
    return V

def values(steps, pub_switch):
    """Return (V(b) for b=0..T, sum-rule value)."""
    T = len(steps)
    hard, R = last_writer_structure(steps, pub_switch)
    V = make_solver(T, hard, R, 0)
    root = 1 | (1 << T)
    curve = [V(T, root, b) for b in range(T + 1)]
    Vs = make_solver(T, hard, R, 1)
    return curve, Vs(T, root, T)

def summarize(curve, sumv):
    T = len(curve) - 1
    rule_p = curve[T]
    clock = min(B for B in range(T + 2) if B > T or curve[min(B, T)] <= B)
    return rule_p, clock, sumv

# ---- families ----
def constant_reader(T):
    return [('S', 0, True)] + [('L', 0, True)] * (T - 1)

def ladder(seq):
    return [('X', a, False) for a in seq]

def round_robin(T, M):
    return [i % M for i in range(T)]

def random_seq(T, M, rng):
    return [rng.randrange(M) for _ in range(T)]

def random_store_heavy(T, M, pstore, rng):
    out = []
    for i in range(T):
        out.append(('S' if rng.random() < pstore else 'L', rng.randrange(M), False))
    return out

def regress():
    """Reproduce the table of node_game_with_range_challenges.py with PUB off and b = infinity (ranges) / b = 0 (no ranges)."""
    print("T  chain  const_reader(no ranges)  const_reader(ranges)")
    for T in range(2, 15):
        # chain: every step a store-free register step; model as stores to distinct public addresses
        ch = [('S', 100 + i, True) for i in range(T)]
        hc, Rc = last_writer_structure(ch, False)
        Vc = make_solver(T, hc, Rc, 0)
        hk, Rk = last_writer_structure(constant_reader(T), False)
        Vk = make_solver(T, hk, Rk, 0)
        root = 1 | (1 << T)
        print(T, Vc(T, root, 0), Vk(T, root, 0), Vk(T, root, T), flush=True)
    rng = random.Random(20261127)
    print("random RAM DAGs (4 addresses, store prob 0.4): T, no-ranges value, ranges value")
    for T in (8, 10, 12, 13):
        for rep in range(3):
            # replicate random_ram's draw order exactly: address first, then store coin
            steps = []
            for i in range(T):
                a = rng.randrange(4)
                steps.append(('S' if rng.random() < 0.4 else 'L', a, False))
            h, R = last_writer_structure(steps, False)
            Vr = make_solver(T, h, R, 0)
            root = 1 | (1 << T)
            print(T, rep, Vr(T, root, 0), Vr(T, root, T), flush=True)

if __name__ == "__main__":
    if "--regress" in sys.argv:
        regress(); sys.exit(0)
    Tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    print("# columns: family T M pub | V(b) for b=0..T | ruleP clock sum")
    for T in range(2, Tmax + 1):
        rows = []
        for pub in (False, True):
            rows.append(("const_reader", T, 1, pub, constant_reader(T)))
        M = (T + 1) // 2
        rows.append(("ladder_rr", T, M, True, ladder(round_robin(T, M))))
        rng = random.Random(1000 + T)
        for rep in range(2):
            rows.append(("ladder_rand%d" % rep, T, M, True, ladder(random_seq(T, M, rng))))
        for M2 in (4, 6):
            rng2 = random.Random(2000 + 10 * T + M2)
            for rep in range(2):
                st = random_store_heavy(T, M2, 0.6, rng2)
                for pub in (False, True):
                    rows.append(("store_heavy%d" % rep, T, M2, pub, st))
        for name, T_, M_, pub, steps in rows:
            curve, sumv = values(steps, pub)
            rp, clock, sv = summarize(curve, sumv)
            print(name, T_, M_, int(pub), "|", " ".join(map(str, curve)), "|", rp, clock, sv, flush=True)
