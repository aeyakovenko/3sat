"""Lemma 5 of notes/frame-game-upper-bound-on-overwrite-ladders.md: minimal blocking sets of the frame DAG of a round-robin
overwrite ladder.
A blocking set B: every path from a source to the sink S_T meets B. Exhaustive over all vertex subsets.
For every minimal blocking set B with lowest layer a, checks
  (i)  B lies in layers [a, Lam(a)], Lam(a) = max over cells c accessed at or after a of the first such access;
  (ii) |B| >= number of distinct cells accessed in steps a..T;
and reports the largest spread (highest - lowest layer + 1) seen; Lemma 5 predicts spread <= C on round robin.
Usage: python3 -I -B frame_dag_minimal_blocking_sets.py [C T ...]   (no argument: 2 6 2 8 3 6 3 7 4 6 2 10)
Writes nothing.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg

def run(C, T):
    seq = ng.round_robin(T, C)
    order, P, tgt = fg.frame_dag(ng.ladder(seq))
    n = len(order); layer = [x[1] for x in order]
    preds = [sum(1 << p for p in ps) for ps in P]
    src = [i for i in range(n) if not P[i]]
    def blocks(B):
        reach = 0                                # nodes reachable from sources avoiding B
        for i in range(n):                       # topological order
            if B >> i & 1: continue
            if not P[i] or (preds[i] & reach):
                reach |= 1 << i
        return not (reach >> tgt & 1)
    acc = [None] + [seq[t - 1] for t in range(1, T + 1)]   # acc[t] = cell accessed at step t
    count = 0; maxspread = 0; bad = 0
    for B in range(1, 1 << n):
        if not blocks(B): continue
        if any(blocks(B & ~(1 << i)) for i in range(n) if B >> i & 1): continue
        count += 1
        ls = [layer[i] for i in range(n) if B >> i & 1]
        a, b = min(ls), max(ls)
        firsts = {}
        for t in range(a, T + 1):
            firsts.setdefault(acc[t], t)
        Lam = max(firsts.values()); cells = len(firsts)
        maxspread = max(maxspread, b - a + 1)
        if b > Lam or bin(B).count('1') < cells:
            bad += 1
            print("VIOLATION", C, T, sorted(order[i] for i in range(n) if B >> i & 1))
    print("C=%d T=%d nodes=%d minimal_blocking_sets=%d max_spread=%d violations=%d" % (C, T, n, count, maxspread, bad), flush=True)

args = list(map(int, sys.argv[1:] or ['2', '6', '2', '8', '3', '6', '3', '7', '4', '6', '2', '10']))
for k in range(0, len(args), 2):
    run(args[k], args[k + 1])
