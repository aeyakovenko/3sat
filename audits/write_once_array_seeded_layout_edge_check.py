"""Layout edge check, written during review, for the seeded packed-presence-table array (Z1+) of
notes/ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md: n = 2^(w/2) updates (all updates, the
worst case for region size), with RS fixed from w as in the note. The region overflow at w = 16, beta = 1 is
expected; w >= 18 fits.

Run from audits/: python3 write_once_array_seeded_layout_edge_check.py   (about 1 s; nothing is written)
"""
import sys, random
sys.dont_write_bytecode = True
from write_once_array_seeded_independent_simulator import Z1plus, good_seed, Violation
for w, beta in [(16, 1), (18, 1), (20, 1), (20, 2), (22, 1)]:
    n = 1 << (w // 2)
    S = Z1plus(w, beta, good_seed(w, random.Random(1)))
    rng = random.Random(2)
    try:
        for t in range(n):
            S.update(rng.randrange(1 << w), t + 1)
        print("w=%d beta=%d n=%d RS=%d: all %d updates fit" % (w, beta, n, S.RS, n))
    except Violation as ex:
        print("w=%d beta=%d n=%d RS=%d: %s" % (w, beta, n, S.RS, ex))
