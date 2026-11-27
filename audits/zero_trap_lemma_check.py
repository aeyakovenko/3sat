#!/usr/bin/env python3
"""Finite check of Lemma A (zero trap) and Lemma B (STORE at the cursor) of
notes/six-instruction-control-classes-in-the-five-slot-machine.md, Section 4,
for the register-payload members of the failing parity row:
  cycle  x <- M[y];  y <- y+x | y-x | x-y;  STORE M[a] <- b, a,b in {x,y};  order LSA or LAS,
  started from public y0, x0 (y0 may be odd: set by the prologue numerical instruction).

Predictions checked on synthetic even periodic bases (w=16):
  T1 (zero trap; STORE M[x]<-x, M[x]<-y, or M[y]<-x in order LSA): after the first read of
     an original tail word at a non-exceptional address a, no further original word is
     read.  Exceptional: a+R, a-R, R-a or its negative lies in P = H u {x0, y0}.
  T2 (STORE at y in order LAS): every LOAD after the first reads a cell written before
     (anywhere in memory), so at most the first LOAD returns an original word.
  T3 (self-mark M[y]<-y, order LSA): y+x: every original read after the first turn is at
     an even address; y-x and x-y: every original read after the first turn is at
     address 0 or at -y0.
Exits are ignored (continuing run).  Prints the number of runs and violations.
"""
import random

W = 16
Q = 1 << W
MASK = Q - 1


def make_base(rng, k):
    # header words: even, bytes in [32,126]; tail words: even, bytes in [10,56]; last word small
    def word(lo, hi):
        b0 = rng.randrange(lo, hi + 1) & ~1
        b1 = rng.randrange(lo, hi + 1)
        return (b1 << 8) | max(b0, lo + (lo & 1))
    header = [word(32, 126) for _ in range(6)]
    nvals = rng.randrange(1, 4)
    tails = [word(10, 56) for _ in range(nvals)]
    mem = {}
    for i, v in enumerate(header):
        mem[i] = v
    lo = len(header)
    for i in range(k):
        mem[lo + i] = tails[i % nvals]
    last = lo + k
    mem[last] = 10  # final newline word, zero padded
    L = last + 1
    return mem, lo, lo + k, L, set(header) | set(tails) | {10, 0}


def run(mem0, lo, hi, L, H, op, sa, sp, order, y0, x0, turns):
    mem = dict(mem0)
    written = set()
    P = set(H) | {x0 & MASK, y0 & MASK}
    regs = {'x': x0 & MASK, 'y': y0 & MASK}
    reads = []  # (turn, address) of original reads inside the input region
    fresh = []  # turns whose LOAD read a cell never written before (anywhere)
    for t in range(turns):
        for ins in order:
            if ins == 'L':
                a = regs['y']
                if a < L and a not in written:
                    reads.append((t, a))
                if a not in written:
                    fresh.append(t)
                regs['x'] = mem.get(a, 0)
            elif ins == 'S':
                a = regs[sa]
                mem[a] = regs[sp]
                written.add(a)
            else:
                xv, yv = regs['x'], regs['y']
                regs['y'] = ((yv + xv) if op == 'y+x' else (yv - xv) if op == 'y-x' else (xv - yv)) & MASK
    return reads, P, fresh


def exceptional(a, R, P):
    vs = [(a + R) & MASK, (a - R) & MASK, (R - a) & MASK]
    vs += [(-v) & MASK for v in vs]
    return any(v in P for v in vs)


def main():
    rng = random.Random(7)
    stats = {'T1': [0, 0, 0], 'T2': [0, 0, 0], 'T3': [0, 0, 0]}  # runs, violations, max tail reads
    informative = 0
    for trial in range(12):
        k = rng.choice([300, 1000, 3000])
        mem0, lo, hi, L, H = make_base(rng, k)
        for op in ('y+x', 'y-x', 'x-y'):
            for sa in ('x', 'y'):
                for sp in ('x', 'y'):
                    for order, entry in [(o, e) for o in ('LSA', 'LAS') for e in range(3)]:
                        # entry e rotates the cyclic order, so the first partial turn may run
                        # the STORE and/or the numerical site on the public x0, y0 first
                        y0 = rng.randrange(Q) if rng.random() < 0.25 else rng.randrange(L) | 1
                        x0 = rng.randrange(Q) if rng.random() < 0.5 else 0
                        rot = order[entry:] + order[:entry]
                        reads, P, fresh = run(mem0, lo, hi, L, H, op, sa, sp, rot, y0, x0, 3 * Q)
                        P |= {(y0 + x0) & MASK, (y0 - x0) & MASK, (x0 - y0) & MASK}
                        tail_reads = [(t, a) for (t, a) in reads if lo <= a < hi]
                        if sa == 'y' and order == 'LAS':
                            key = 'T2'
                            # exact form of Lemma B (LAS): no LOAD after the first reads an
                            # unwritten cell, inside or outside the input region
                            bad = any(t >= 1 for t in fresh)
                        elif sa == 'y' and sp == 'y':
                            key = 'T3'
                            later = [a for (t, a) in reads[1:]]
                            pub = {(-y0) & MASK, (-(y0 + x0)) & MASK, (-(y0 - x0)) & MASK, (-(x0 - y0)) & MASK,
                                   (y0 + x0) & MASK, (y0 - x0) & MASK, (x0 - y0) & MASK, y0 & MASK}
                            lastf = (L - 1 - mem0[L - 1]) & MASK
                            if op == 'y+x':
                                bad = any(a % 2 and a not in pub for a in later)
                            else:
                                bad = any(a not in ({0, lastf} | pub) for a in later)
                        else:
                            key = 'T1'
                            bad = False
                            for i, (t, a) in enumerate(tail_reads):
                                if not exceptional(a, mem0[a], P):
                                    if any(t2 > t for (t2, _) in reads):
                                        bad = True
                                    break
                        informative += int(len(tail_reads) > 0)
                        st = stats[key]
                        st[0] += 1
                        st[1] += int(bad)
                        st[2] = max(st[2], len(set(a for _, a in tail_reads)))
    print('runs that read at least one original tail word:', informative)
    for key, (n, v, m) in stats.items():
        print(f'{key}: runs={n} violations={v} max distinct original tail reads in a run={m}')


if __name__ == '__main__':
    main()
