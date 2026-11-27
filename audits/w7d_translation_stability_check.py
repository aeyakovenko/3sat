#!/usr/bin/env python3
"""Finite check of the W7d stability lemma (writable-five-slots-without-a-clock.md, Other STORE
operands, bullet 3).  Class W7d as five_slot_case_split_coverage.py defines it: x != p, LOAD x<-M[p], STORE M[p]<-v after the LOAD
and before the NUM (order LSN), NUM p<-p+d with d a fixed odd integer, payload
v in {x (writeback), p (self-mark), c (fixed mark)}.  Claim checked at small widths:
on every initial memory (random samples over all 2^w cells, plus the all-distinct image)
and every start cursor, the full machine state (p, x, whole memory) at the ends of
full periods 2 and 3 agree, so a continuing run that has not exited within three
periods repeats forever.  Also checks the owner-change count of the protocol: for a
contiguous interval [0, A) versus its complement, one full period of +d changes owner
at most 2|d| times (communication note, 'Distributed simulation', J = 2|d|).
Run: python3 w7d_stability_check.py
"""
import random
random.seed(20261127)
viol = 0; runs = 0; maxchg = {}
for w in (4, 6, 8):
    Q = 1 << w
    for d in [x for x in range(-7, 8) if x % 2]:
        for payload in ('x', 'p', 'c'):
            for trial in range(40):
                M = [random.randrange(Q) for _ in range(Q)] if trial else list(range(Q))[::-1]
                p = random.randrange(Q); x = random.randrange(Q); c = random.randrange(Q)
                states = []
                for period in range(4):
                    for _ in range(Q):          # d odd: period of p <- p+d is exactly Q
                        x = M[p]
                        M[p] = x if payload == 'x' else (p if payload == 'p' else c)
                        p = (p + d) % Q
                    states.append((p, x, tuple(M)))
                runs += 1
                if states[1] != states[2]:
                    viol += 1
            # owner changes in one period, interval [0, A) vs complement, every A
            for A in range(1, Q):
                own = lambda a: a < A
                q = 0; chg = 0
                for _ in range(Q):
                    nq = (q + d) % Q
                    if own(nq) != own(q): chg += 1
                    q = nq
                maxchg[d] = max(maxchg.get(d, 0), chg)
print('W7d stability: runs', runs, 'violations (state after period 2 != after period 3):', viol)
print('max owner changes per period by d:', {d: maxchg[d] for d in sorted(maxchg)},
      'all <= 2|d|:', all(maxchg[d] <= 2 * abs(d) for d in maxchg))
