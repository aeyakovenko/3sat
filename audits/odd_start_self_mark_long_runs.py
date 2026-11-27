#!/usr/bin/env python3
"""Rerun the worst self-mark case of odd_start_self_mark_escape.py (k=2000, R=0x2422, y+x,
LSA, y0=1001) and the register-payload rows of odd_start_parity_rows.py at 2,000,000 turns."""
import sys
sys.dont_write_bytecode = True   # importing the sibling script leaves no __pycache__
import odd_start_parity_rows as pr
W = 16; Q = 1 << W; MASK = Q - 1
HEADER = pr.HEADER
def run_selfmark(k, R, op, order, y0, steps):
    mem = {i: v for i, v in enumerate(HEADER)}
    lo, hi = len(HEADER), len(HEADER) + k
    for i in range(lo, hi): mem[i] = R
    written = set(); reads = set(); x = 0; y = y0
    for _ in range(steps):
        for ins in order:
            if ins == 'L':
                if lo <= y < hi and y not in written: reads.add(y)
                x = mem.get(y, 0)
            elif ins == 'S':
                mem[y] = y; written.add(y)
            else:
                y = ((y + x) if op == 'y+x' else (y - x) if op == 'y-x' else (x - y)) & MASK
    return len(reads)
print('self-mark worst case k=2000 R=0x2422 y+x LSA y0=1001:', [(T, run_selfmark(2000, 0x2422, 'y+x', 'LSA', 1001, T)) for T in (16000, 2000000)], flush=True)
worst = 0; arg = None
for op in ('y+x', 'y-x', 'x-y'):
    for sa in ('x', 'y', 'z'):
        for sp in ('x', 'y'):
            for order in ('LSA', 'LAS'):
                for y0 in (1, 9, 0x8001):
                    for z in (1, 0x8001):
                        c = pr.run(500, op, sa, sp, order, y0, z, 2000000)
                        if c > worst: worst, arg = c, (op, sa, sp, order, y0, z)
print('register-payload rows (payload x or y), k=500, 2,000,000 turns: max distinct original tail reads =', worst, 'at', arg, flush=True)
