#!/usr/bin/env python3
"""The landmark decode inside the chart's evaluator uses at most h forward probes
(proof: a decode walks from the preceding mark M' to the next mark M through y, and
dist(M', M) <= h; on an unmarked cycle it walks the cycle, of length <= h).
Exhaustive over all permutations of m <= 8 and all h = 1..m, with the evaluator's own code."""
from itertools import permutations
import sys
sys.dont_write_bytecode = True      # importing the checker leaves no __pycache__ in audits/
import landmark_shared_bank_chart_check as L
n = 0; tight = 0
for m in range(2, 9, 2):
    for f in permutations(range(m)):
        data = L.pinned_file(list(f))
        for h in range(1, m + 1):
            ev = L.Evaluator(data, L.encode_bank(m, 1, h, L.landmark_pairs(f, h)), 'main', h)
            ev.c = 0; ev._header(); ev._bankhdr()
            for a in range(m):
                j = ev._decode(a)
                assert f[j] == a and ev.probes <= h, (f, h, a, ev.probes)
                tight += ev.probes == h
                n += 1
print(f"{n} decodes (m = 2,4,6,8; every permutation; h = 1..m): all correct, probes <= h; "
      f"{tight} decodes use exactly h probes")
