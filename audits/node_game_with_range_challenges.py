"""Exact two-person pebble game (Dymond-Tompa style) on small RAM access DAGs,
with and without the 'last-writer range challenge'.

Nodes 0..T: node u = machine state after step u (node 0 = initial state, always known).
Step i (1..T) is either a store or a load. hard(i) = {i-1} plus {p(i)} for a load whose
last writer p(i) >= 1.  For a load, the claim 'p(i) is the last writer' is disputed by a
range challenge: the challenger names a step k in (p(i), i); the pebbler must exhibit the
state node k-1 (which fixes step k's address), i.e. a node u in R(i) = [p(i), i-2].

Game (cost = number of pebble placements, pebbler minimises, challenger maximises):
  state (c, P): c challenged node, P pebbled set (bitmask, contains node 0 and c).
  Pebbler option B: place a pebble on v not in P: cost 1 + max(V(v, P+v), V(c, P+v)).
  Pebbler option A (only if hard(c) is inside P): declare ready. Challenger then accepts
    (cost 0) or, if ranges are on, names u in R(c): if u in P it was accepted earlier
    (cost 0); otherwise pebbler places u (cost 1) and challenger may challenge it:
    cost 1 + V(u, P+u).
This is the game of the round-two QBF entry, unchanged.
Usage: python3 node_game_with_range_challenges.py   (prints the chain, the constant reader
with and without range challenges, and twelve random RAM DAGs)
"""
import sys, random
from functools import lru_cache

def game_value(T, hard, R, use_ranges):
    full = (1 << (T + 1)) - 1
    hardmask = [0] * (T + 1)
    for i in range(1, T + 1):
        for h in hard[i]:
            hardmask[i] |= 1 << h
    sys.setrecursionlimit(100000)

    @lru_cache(maxsize=None)
    def V(c, P):
        best = None
        if hardmask[c] & ~P == 0:
            val = 0
            if use_ranges:
                for u in R[c]:
                    if not (P >> u) & 1:
                        val = max(val, 1 + V(u, P | (1 << u)))
            best = val
            if best == 0:
                return 0
        free = full & ~P
        v = 1
        while free >> v:
            if (free >> v) & 1:
                Q = P | (1 << v)
                val = 1 + max(V(v, Q), V(c, Q))
                if best is None or val < best:
                    best = val
            v += 1
        return best

    return V(T, 1 | (1 << T))

def chain(T):
    hard = [[]] + [[i - 1] for i in range(1, T + 1)]
    R = [[] for _ in range(T + 1)]
    return hard, R

def constant_reader(T):
    # step 1 stores to address 0; every later step loads address 0 (last writer = step 1)
    hard = [[], [0]] + [[i - 1, 1] for i in range(2, T + 1)]
    R = [[], []] + [list(range(1, i - 1)) for i in range(2, T + 1)]
    return hard, R

def random_ram(T, addrs, pstore, rng):
    last = {}
    hard = [[]]; R = [[]]
    for i in range(1, T + 1):
        a = rng.randrange(addrs)
        if rng.random() < pstore:
            last[a] = i
            hard.append([i - 1]); R.append([])
        else:
            p = last.get(a, 0)
            h = [i - 1] + ([p] if p >= 1 and p != i - 1 else [])
            hard.append(h)
            R.append(list(range(max(p, 1), i - 1)))  # node 0 is known, so start at 1
    return hard, R

if __name__ == "__main__":
    print("T  chain  const_reader(no ranges)  const_reader(ranges)")
    for T in range(2, 15):
        hc, Rc = chain(T)
        hk, Rk = constant_reader(T)
        print(T, game_value(T, hc, Rc, False), game_value(T, hk, Rk, False),
              game_value(T, hk, Rk, True), flush=True)
    rng = random.Random(20261127)
    print("random RAM DAGs (4 addresses, store prob 0.4): T, no-ranges value, ranges value")
    for T in (8, 10, 12, 13):
        for rep in range(3):
            h, R = random_ram(T, 4, 0.4, rng)
            print(T, rep, game_value(T, h, R, False), game_value(T, h, R, True), flush=True)
