#!/usr/bin/env python3
"""Long-horizon reruns (several laps of Q = 2^16) of the parity-row members, to remove
the turn-horizon limitation of odd_start_parity_rows.py / odd_start_self_mark_escape.py."""
import sys
sys.dont_write_bytecode = True   # importing the sibling script leaves no __pycache__
from odd_start_parity_rows import run
cases = [
    ('fixed odd marker M[y]<-z, z=1', lambda T: run(500, 'y+x', 'y', 'z', 'LSA', 9, 1, T)),
    ('fixed odd marker M[y]<-z, z=1, k=2000', lambda T: run(2000, 'y+x', 'y', 'z', 'LSA', 9, 1, T)),
    ('fixed odd marker M[y]<-z, z=3, y-x', lambda T: run(500, 'y-x', 'y', 'z', 'LSA', 9, 3, T)),
    ('self-mark M[y]<-y, y+x, k=500', lambda T: run(500, 'y+x', 'y', 'y', 'LSA', 9, 1, T)),
]
for name, f in cases:
    print(name, [(T, f(T)) for T in (100000, 1000000, 3000000)], flush=True)
