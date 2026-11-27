"""Exhaustive native-RAM search for the one-pair sign-plane catalog F(w,1).

Words P (address 0) and M (address 1) of w bits; the file is satisfiable iff
P & M == 0 and M != 2^w-1.  The search asks whether ANY program with at most
`steps` executed instructions is correct on a pinned test suite; a negative
answer on the suite is a lower bound for the full catalog.  It runs the search
`Machine` of split_word_sat_adaptive_audit.py unchanged, at width w.
Test suite (analogue of that audit's six-bit pinned suite P<4, M in 4..7):
  P in {0,1,2,3},  M in {2^w-4,...,2^w-1}.
Usage: python3 one_sign_plane_pair_native_search.py w steps
With no arguments it runs the calibration at w=3 with at most 4 and at most 5 steps.
Written for four-instructions-per-sign-plane-pair-at-every-width.md.
"""
import sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(10000)
from split_word_sat_adaptive_audit import Machine, mask, sat


def search(w, steps):
    top = (1 << w) - 1
    samples = [(p, m) for m in range(top - 3, top + 1) for p in range(4)]
    machine = Machine(w, samples)
    target = mask(sat(p, m, w) for p, m in samples)
    # closed form agrees with brute-force sat on the suite
    assert all(sat(p, m, w) == ((p & m) == 0 and m != top) for p, m in samples)
    t0 = time.time()
    found = machine.decision_search(target)(machine.domain, steps)
    print(f"w={w} suite={len(samples)} inputs (P<4, M>={top-3}) target_mask={target:#x} "
          f"steps<={steps}: program exists = {found}  ({time.time()-t0:.1f}s)", flush=True)
    return found


if __name__ == "__main__":
    if len(sys.argv) > 1:
        search(int(sys.argv[1]), int(sys.argv[2]))
    else:
        assert not search(3, 4) and search(3, 5)
