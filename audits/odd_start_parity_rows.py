#!/usr/bin/env python3
"""Finite check of the parity rows of the five-slot case split when a prologue
numerical instruction makes the cursor (or a fixed operand) odd.

Class: five-slot writable cycle {LOAD, STORE, numerical} + one prologue numerical
instruction (classes 'L1S1A2B2  C:ALS / C:ASL  pre:A' in six_slot_control_classes.tsv).

Five-slot row (five-instruction-loops-on-dimacs-sat.md, "The ALU uses both mutable
registers"): with x <- M[y] and y <- y+x, y-x or x-y, and a STORE copying a register,
all data stay even on the even periodic base because every register starts at 0 or at
the even metadata n, w.  A prologue numerical instruction can instead set y to an odd
public word.  This script runs the continuing cycle (no exits) on a synthetic periodic
even base and counts how many distinct sensitive tail words are read while still
original.  Bounded counts mean a missed-original argument may still close the member;
counts growing with the tail length mean the member reads all sensitive words and a
missed-original argument cannot close it.

Synthetic base (w = 16, Q = 2^16): 8 even header words, then k tail words equal to
R = 0x2A20 (even, high byte 42, so |R| >= 10Q/256 as in property 1 of the five-slot
note), zero elsewhere.

Run: python3 odd_start_parity_rows.py [STEPS]   (default 4000 turns per run, at least 4k+2000)
"""
import itertools, sys

W = 16
Q = 1 << W
MASK = Q - 1
R = 0x2A20
HEADER = [0x2070, 0x6E63, 0x2066, 0x3032, 0x3120, 0x3030, 0x3030, 0x0A30]


def base(k):
    mem = {}
    for i, v in enumerate(HEADER):
        mem[i] = v
    for i in range(k):
        mem[len(HEADER) + i] = R
    return mem


def run(k, op, st_addr, st_pay, order, y0, z, steps):
    mem = base(k)
    lo, hi = len(HEADER), len(HEADER) + k
    written = set()
    read_orig = set()
    x, y = 0, y0
    regs = {'x': 0, 'y': y0, 'z': z}
    seen_states = 0
    for t in range(steps):
        for ins in order:
            if ins == 'L':
                a = regs['y']
                if lo <= a < hi and a not in written:
                    read_orig.add(a)
                regs['x'] = mem.get(a, 0)
            elif ins == 'S':
                a = regs[st_addr]
                mem[a] = regs[st_pay]
                written.add(a)
            else:
                xv, yv = regs['x'], regs['y']
                if op == 'y+x':
                    regs['y'] = (yv + xv) & MASK
                elif op == 'y-x':
                    regs['y'] = (yv - xv) & MASK
                elif op == 'x-y':
                    regs['y'] = (xv - yv) & MASK
                elif op == 'y+z':
                    regs['y'] = (yv + regs['z']) & MASK
                elif op == 'x+z':
                    regs['y'] = (xv + regs['z']) & MASK
    return len(read_orig)


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    ks = [500, 2000]
    y0s = [1, 9, 0x101, 0x8001]
    zs = [1, 0x8001]
    ops = ['y+x', 'y-x', 'x-y']
    stores = [(a, p) for a in ('x', 'y', 'z') for p in ('x', 'y', 'z')]
    orders = ['LSA', 'LAS']
    print(f'steps per run = {steps}; tail lengths k = {ks}')
    print('op  STORE(addr<-payload)  order  max over (y0,z) of distinct original tail reads, per k')
    growing = []
    for op in ops:
        for (sa, sp) in stores:
            for order in orders:
                row = []
                for k in ks:
                    best = 0
                    for y0 in y0s:
                        for z in zs:
                            best = max(best, run(k, op, sa, sp, order, y0, z, max(steps, 4 * k + 2000)))
                    row.append(best)
                flag = 'GROWS' if row[-1] >= ks[-1] // 4 else ''
                if flag:
                    growing.append((op, sa, sp, order, row))
                print(f'{op:4s} M[{sa}]<-{sp}  {order}  {row} {flag}')
    print('\nrows whose count reaches k/4 at the largest k:', len(growing))
    for g in growing:
        print('  ', g)


if __name__ == '__main__':
    main()
