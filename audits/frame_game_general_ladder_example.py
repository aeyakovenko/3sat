#!/usr/bin/env python3
"""The general-ladder example of notes/frame-value-on-round-robin-ladders.md (Section 4): exact frame value of the ladder 0, 1, .., C-1
followed by T-C accesses of cell 0, by the exact Dymond-Tompa solver frame_dag_dymond_tompa_value.cpp (built by
frame_dag_solvers.py), against the round-robin lower bound g_rec(T).
Run from audits/: python3 frame_game_general_ladder_example.py [C T [cap_log2]]   (default 3 40 24, about a second,
under an 8 GB address-space limit; C = 4, T = 40 fills the memo at a lower bound in about 4 s). Nothing is written.
"""
import sys, os, subprocess, resource
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import truth_claim_frame_game as fg
import frame_dag_solvers as solvers
import frame_game_round_robin_recursion as rec

args = sys.argv[1:] or ['3', '40', '24']
C, T = int(args[0]), int(args[1])
lg = args[2] if len(args) > 2 else '24'
binary = solvers.binary('dt')
addrs = list(range(C)) + [0] * (T - C)
order, P, tgt = fg.frame_dag([('X', a, False) for a in addrs])
inp = f"{len(order)} {tgt}\n" + "".join(f"{len(p)} {' '.join(map(str, p))}\n" for p in P)
cap = lambda: resource.setrlimit(resource.RLIMIT_AS, (8 << 30, 8 << 30))
out = subprocess.run([binary, '40', lg], input=inp, capture_output=True, text=True, timeout=1100, preexec_fn=cap).stdout.strip().splitlines()
g = rec.grec(C, T)[T]
print(f"ladder 0..{C-1} then 0^{T-C}: n={len(order)} frame_dt: {out[-1]} | round robin (C={C}, T={T}): g_rec={g}, f_C={rec.fC(C, T)}")
