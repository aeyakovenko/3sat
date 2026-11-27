#!/usr/bin/env python3
"""Adversarial variant of odd_start_parity_rows.py for the only STORE choice that can leave
the zero trap: the self-mark M[y] <- y (y <- y+x, y-x or x-y; orders LSA and LAS).
Varies the repeated tail word R over even words whose bytes lie in [10, 56] (the
five-slot base's byte range), and the odd public initial cursor y0, at w = 16.
Reports the maximum number of distinct original tail words read on the continuing run."""
import random, sys
W = 16; Q = 1 << W; MASK = Q - 1
HEADER = [0x2070, 0x6E63, 0x2066, 0x3032, 0x3120, 0x3030, 0x3030, 0x0A30]
def run(k, R, op, order, y0, steps):
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
rng = random.Random(1)
Rs = []
while len(Rs) < 40:
    lo_b = rng.randrange(10, 57) & ~1; hi_b = rng.randrange(10, 57)
    Rs.append((hi_b << 8) | lo_b)
y0s = [1, 3, 9, 11, 101, 1001, 0x8001, 0xFFFF, 0x4001]
for k in (500, 2000):
    best = (0, None)
    for R in Rs:
        for op in ('y+x', 'y-x', 'x-y'):
            for order in ('LSA', 'LAS'):
                for y0 in y0s:
                    c = run(k, R, op, order, y0, 6 * k + 4000)
                    if c > best[0]: best = (c, (hex(R), op, order, y0))
    print(f'k={k}: max distinct original tail reads = {best[0]} at {best[1]}  (40 R values x 3 ops x 2 orders x {len(y0s)} y0)')
