#!/usr/bin/env python3
"""Independent check of Lemmas A and B of
notes/six-instruction-control-classes-in-the-five-slot-machine.md, Section 4, written during
review from the lemma statements, not from zero_trap_lemma_check.py.

Run: python3 zero_trap_lemma_independent_check.py [--seed N] [--edge] [--norm-floor-cq]
  --seed N         random seed (default 1); the review ran seeds 1, 2 and 3
  --edge           edge-case bases: tail values next to Q/2 (the largest allowed), values with
                   2R = Q - a for a tail address a, and the smallest allowed norm 2L+1; last
                   word f = L-2 or f = 1 (the review ran seeds 11 and 12)
  --norm-floor-cq  draw tail values of norm above cQ only, not above max(cQ, 2L), as the
                   review's first generator did. This breaks the Setting's hypothesis that every
                   full word has norm above 2L (at Q = 4096, L = 100, cQ = 160); with seed 1 it
                   reports 4 violations.
Each run takes about 35 s.

Base image (the lemma's Setting, deliberately more general than DIMACS):
  I=[0,L); zero outside; every word in I nonzero and < Q/2; every full word of
  norm > 2L (odd and even values allowed); last word f small (1..L-2);
  tail words (a block of k addresses) drawn from a few values of norm >= cQ.
Cycle: x<-M[y]; y<-y+x | y-x | x-y; STORE M[a]<-b, a,b in {x,y}; order LSA or LAS;
entry at any of the three data instructions with public y0,x0.
Checks:
  A-rows: number of distinct NON-exceptional tail addresses whose original word is
          read is <= 1, and after the first one the cursor is confined to {v} (y+-x)
          or {v,-v} (x-y), both cells 0.
  B-LAS (STORE at y, order LAS): no original word is read after the first LOAD.
  B-self (M[y]<-y, LSA): every position of I loaded after the first LOAD is even (y+x),
          in {0,L-1-f} (y-x), in {0,L-1-f,-p1} (x-y), p1 = first LOAD position.
"""
import argparse, random, sys

NORM_FLOOR_2L = True   # False under --norm-floor-cq

def build(Q, L, k, ntail, rng, c=10/256):
    M = {}
    lo2 = 2 * L + 1
    tail_vals = []
    while len(tail_vals) < ntail:
        lo = max(int(c * Q), 2 * L) if NORM_FLOOR_2L else int(c * Q)
        r = rng.randrange(lo + 1, Q // 2)  # Setting: full words have norm > 2L
        tail_vals.append(r)
    t0 = rng.randrange(1, L - k - 1)
    for a in range(L - 1):
        if t0 <= a < t0 + k:
            M[a] = rng.choice(tail_vals)
        else:
            M[a] = rng.randrange(lo2, Q // 2)   # header/other full words, any parity
    f = rng.randrange(1, L - 1)
    M[L - 1] = f
    return M, set(range(t0, t0 + k)), tail_vals, f

def edge_build(Q, L, k, ntail, rng, c=10/256):
    M, tail, tv, f = build(Q, L, k, ntail, rng, c)
    ts = sorted(tail)
    a0 = ts[0] if ts[0] % 2 == 0 else ts[1]
    cands = [Q // 2 - 1, (Q - a0) // 2, 2 * L + 1, Q // 2 - L]
    vals = rng.sample(cands, rng.choice([1, 2, 3]))
    for i, a in enumerate(ts):
        M[a] = vals[i % len(vals)]
    f = rng.choice([1, L - 2])
    M[L - 1] = f
    return M, tail, vals, f

def norm(u, Q):
    u %= Q
    return min(u, Q - u)

def run(Q, M0, tail, op, order, st, ent, y0, x0, turns):
    M = dict(M0)
    y, x = y0 % Q, x0 % Q
    seq = ['L', 'S', 'A'] if order == 'LSA' else ['L', 'A', 'S']
    i = seq.index(ent)
    written = set()
    loads = []  # (turn, address, value, original?)
    public_words = {y, x}
    first_load_seen = False
    pre_partial = []  # words of the partial turn before the first LOAD
    nturn = 0
    steps = 0
    while nturn < turns:
        ins = seq[i]
        if ins == 'L':
            v = M.get(y, 0)
            orig = (y not in written)
            loads.append((nturn, y, v, orig))
            x = v
            first_load_seen = True
            nturn += 1
        elif ins == 'A':
            if op == 'y+x': y = (y + x) % Q
            elif op == 'y-x': y = (y - x) % Q
            else: y = (x - y) % Q
            if not first_load_seen: pre_partial.append(y)
        else:
            a = x if st[0] == 'x' else y
            b = x if st[1] == 'x' else y
            M[a] = b
            written.add(a)
            if not first_load_seen: pre_partial += [a, b]
        i = (i + 1) % 3
    return loads, pre_partial

def main():
    parser = argparse.ArgumentParser(description='Independent check of the zero-trap lemmas.')
    parser.add_argument('--seed', type=int, default=1, help='random seed (default 1)')
    parser.add_argument('--edge', action='store_true', help='edge-case tail values and last words')
    parser.add_argument('--norm-floor-cq', action='store_true',
                        help='tail values of norm above cQ only (breaks the norm hypothesis)')
    args = parser.parse_args()
    global NORM_FLOOR_2L
    NORM_FLOOR_2L = not args.norm_floor_cq
    make = edge_build if args.edge else build
    rng = random.Random(args.seed)
    stats = {}
    viol = []
    informative = 0
    configs = [(4096, 60, 30), (4096, 100, 70), (65536, 400, 300)]
    for (Q, L, k) in configs:
        for base in range(6 if Q == 4096 else 2):
            M0, tail, tvals, f = make(Q, L, k, rng.choice([1, 2, 3]), rng)
            H = set(M0.values()) | {0}
            for op in ('y+x', 'y-x', 'x-y'):
                for order in ('LSA', 'LAS'):
                    for st in ('xx', 'xy', 'yx', 'yy'):
                        for ent in ('L', 'S', 'A'):
                            for trial in range(4 if Q == 4096 else 2):
                                r = rng.random()
                                if r < 0.5: y0 = rng.choice(sorted(tail))
                                elif r < 0.75: y0 = rng.randrange(0, L)
                                else: y0 = rng.randrange(0, Q)
                                x0 = rng.choice([0, rng.randrange(0, Q), rng.choice(sorted(tail))])
                                turns = 2 * Q
                                loads, pre = run(Q, M0, tail, op, order, st, ent, y0, x0, turns)
                                P = H | {y0 % Q, x0 % Q} | set(w % Q for w in pre)
                                Pn = P | {(-u) % Q for u in P}
                                # exceptional tail addresses
                                def exceptional(a):
                                    R = M0[a]
                                    return any(((a + R) % Q) in Pn or ((a - R) % Q) in Pn or ((R - a) % Q) in Pn for _ in [0])
                                otail = [(t, a) for (t, a, v, o) in loads if o and a in tail]
                                if otail: informative += 1
                                row = (op, order, st)
                                stats.setdefault(row, [0, 0])
                                stats[row][0] += 1
                                isA = st in ('xx', 'xy') or (st == 'yx' and order == 'LSA')
                                isBLAS = st[0] == 'y' and order == 'LAS'
                                isSelf = st == 'yy' and order == 'LSA'
                                if isA:
                                    nonexc = sorted(set(a for (t, a) in otail if not exceptional(a)))
                                    ok = len(nonexc) <= 1
                                    if nonexc:
                                        # first such read and the confinement afterwards
                                        tfirst = min(t for (t, a) in otail if a == nonexc[0])
                                        after = [(a, v) for (t, a, v, o) in loads if t > tfirst]
                                        if after:
                                            vpos = after[0][0]
                                            allowed = {vpos} if op != 'x-y' else {vpos, (-vpos) % Q}
                                            if any(a not in allowed or val != 0 for (a, val) in after):
                                                ok = False
                                    stats[row][1] += 0 if ok else 1
                                    if not ok: viol.append((Q, L, row, ent, y0, x0, nonexc[:5]))
                                elif isBLAS:
                                    later = [a for (t, a, v, o) in loads[1:] if o]
                                    ok = len(later) == 0
                                    stats[row][1] += 0 if ok else 1
                                    if not ok: viol.append((Q, L, row, ent, y0, x0, later[:5]))
                                elif isSelf:
                                    p1 = loads[0][1]
                                    inI = [a for (t, a, v, o) in loads[1:] if a < L]
                                    if op == 'y+x': bad = [a for a in inI if a % 2 == 1 and a != p1]
                                    elif op == 'y-x': bad = [a for a in inI if a not in (0, L - 1 - f, p1)]
                                    else: bad = [a for a in inI if a not in (0, L - 1 - f, p1, (-p1) % Q)]
                                    ok = not bad
                                    stats[row][1] += 0 if ok else 1
                                    if not ok: viol.append((Q, L, row, ent, y0, x0, bad[:5]))
                                else:
                                    raise SystemExit('unclassified row ' + str(row))
    tot = sum(v[0] for v in stats.values()); bad = sum(v[1] for v in stats.values())
    print('subrows', len(stats), 'runs', tot, 'informative (read >=1 original tail word)', informative, 'violations', bad)
    for v in viol[:10]: print('VIOLATION', v)

if __name__ == '__main__':
    main()
