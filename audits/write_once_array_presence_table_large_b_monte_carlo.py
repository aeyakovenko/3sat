#!/usr/bin/env python3
"""One-level Monte Carlo of the per-level costs of the packed-presence-table array of
notes/packed-presence-tables-for-a-word-write-once-array.md at large B (interior level, N << m limit),
written during review.

Merge: one input coarse bucket = B output coarse buckets; each of the B input runs has Poisson(1) keys
there (Bin(B^(l-1), B^-(l-1)) in the limit), uniform and distinct.  The selection rounds are run exactly as
the note describes (per round, per flagged run: 1 bit-scan probe + 1 directory probe + a scan
from the input bucket's start to the first key in b above the last output).  Fixed per-output-bucket
terms: 3 per output key (value load, key write, value write), 1 directory write, presence words
(old load + new write when k > 0, i.e. 2 - 1/B on average), input presence word 1/B.
Read: d runs at the level (d uniform on 1..B-1, the digit given it is nonzero); each has Poisson(1)
keys in q's coarse bucket (B fine buckets); flagged iff one lies in q's fine bucket; a flagged run costs
1 bit-scan + 1 directory + keys up to the first key >= q.  No true hits (N << m).
Run from audits/:
  python3 write_once_array_presence_table_large_b_monte_carlo.py
      seed 1, 200,000 trials, B = 8 and 32 (about 7 s); the first two rows of the note's table.
  python3 write_once_array_presence_table_large_b_monte_carlo.py 1 200000 8 32 128 512 2048
      the note's full table (about 6 minutes).
  Usage in general: SEED TRIALS B [B ...]; one random stream serves the B values in the order given.
Nothing is written.
"""
import sys, random, math

def poisson1(rng):
    L, k, p = math.exp(-1.0), 0, 1.0
    while True:
        p *= rng.random()
        if p <= L:
            return k
        k += 1

def merge_input_bucket(B, rng):
    runs = []
    for r in range(B):
        ks = sorted(rng.random() for _ in range(poisson1(rng)))
        runs.append(ks)
    cost = 0.0; outkeys = 0; rounds = 0
    for b in range(B):
        flagged = [r for r in range(B) if any(int(x * B) == b for x in runs[r])]
        cost += 1 + (2 - 1.0 / B) + 1.0 / B           # directory write, presence words, input presence word
        if not flagged:
            continue
        last = -1.0
        while True:
            rounds += 1
            best = None
            for r in flagged:
                cost += 2                               # bit scan + directory cell
                for x in runs[r]:
                    cost += 1                           # key load
                    xb = int(x * B)
                    if xb < b or (xb == b and x <= last):
                        continue
                    if xb == b and (best is None or x < best):
                        best = x
                    break
            if best is None:
                break
            cost += 3; outkeys += 1; last = best
    return cost, outkeys, rounds

def read_level(B, rng):
    d = rng.randrange(1, B)
    q = rng.random()
    fq = int(q * B)
    cost = 1.0; flags = 0
    for _ in range(d):
        ks = sorted(rng.random() for _ in range(poisson1(rng)))
        if any(int(x * B) == fq for x in ks):
            flags += 1
            cost += 2
            for x in ks:
                cost += 1
                if x >= q:
                    break
    return cost, flags

def main():
    argv = sys.argv[1:] or ['1', '200000', '8', '32']
    seed, trials = int(argv[0]), int(argv[1])
    rng = random.Random(seed)
    print('    B  merge/upd   out/upd  rounds/out | read/level  flag/read')
    for B in map(int, argv[2:]):
        nb = max(1, trials // B)
        C = O = R = 0
        for _ in range(nb):
            c, o, r = merge_input_bucket(B, rng); C += c; O += o; R += r
        rc = rf = 0
        for _ in range(trials):
            c, f = read_level(B, rng); rc += c; rf += f
        print(f'{B:5d}  {C / (nb * B):9.3f}  {O / (nb * B):8.3f}  {R / max(O, 1):10.3f} | {rc / trials:10.3f}  {rf / trials:9.3f}')

if __name__ == '__main__':
    main()
