"""Further cases of the algebraic block sum-check of count_splitting_game_check.py, for
counting-sat-under-a-quasi-linear-sat-solver.md.

For each (n, s, d, q, m) it draws seeded bounded-occurrence CNFs whose model count is
nonzero mod q, enumerates every prover table and every challenge in F_q^s, and checks that
the game accepts exactly the residue #phi mod q (three formulas per configuration).
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_splitting_game_check import random_cnf, brute_count, algebraic_game_accepts
done = 0
for (n, s, d, q, m) in [(4, 2, 2, 3, 4), (4, 2, 2, 3, 3), (3, 1, 2, 3, 3), (4, 1, 3, 5, 5)]:
    for seed in range(40):
        cl = random_cnf(n, m, max_occ=d, seed=1000 + seed)
        t = brute_count(cl, n)
        if t % q == 0: continue
        A = algebraic_game_accepts(cl, n, s, d, q)
        print(f"n={n} s={s} d={d} q={q} m={m} seed={1000+seed}: #phi={t}, mod q={t%q}, accepted={sorted(A)}", "OK" if A == frozenset([t % q]) else "FAIL")
        assert A == frozenset([t % q])
        done += 1
        if done % 3 == 0: break
