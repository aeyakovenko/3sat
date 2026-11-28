#!/usr/bin/env python3
"""Independent closure check (Claim 1 of notes/frame-value-on-round-robin-ladders.md), written during review, with its
own frame-DAG builder (frame_game_round_robin_challenger_independent.frame_dag).
Run from audits/: python3 frame_game_focus_closure_independent_check.py [Cmax Tmax]   (default 5 12, about a second;
4,074 round-robin foci plus 52,050 class segments). Nothing is written.
For every node v of the round-robin frame DAG and every s <= layer(v): the induced subgraph on
(anc(v) + v) restricted to layers >= s must equal the frame DAG of the segment a_s..a_{layer(v)-1}, cell(v)
under (mu, c) -> (mu - s + 1, c); and that segment is round robin except possibly its top.
Also: the round-robin + arbitrary-top class, checked directly: for random 'segments' (RR prefix, arbitrary top)
every (node, s) focus again equals the frame DAG of a segment of the same class."""
import sys, random
sys.dont_write_bytecode = True
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frame_game_round_robin_challenger_independent import frame_dag


def graph(addr):
    nodes, preds, sink = frame_dag(addr)
    E = set()
    for j, (mu, c) in enumerate(nodes):
        m = preds[j]; i = 0
        while m:
            if m & 1:
                E.add((nodes[i], (mu, c)))
            m >>= 1; i += 1
    return set(nodes), E, nodes, preds


def check_ladder(addr, C, count):
    V, E, nodes, preds = graph(addr)
    par = {}
    for (u, w) in E:
        par.setdefault(w, []).append(u)
    for v in nodes:
        # ancestors
        anc = {v}; st = [v]
        while st:
            x = st.pop()
            for u in par.get(x, []):
                if u not in anc:
                    anc.add(u); st.append(u)
        top, cv = v
        for s in range(1, top + 1):
            F = {x for x in anc if x[0] >= s}
            FE = {(u, w) for (u, w) in E if u in F and w in F}
            seg = [None] + [addr[t] for t in range(s, top)] + [cv]
            # class membership: seg[1..L-1] consecutive round robin
            for i in range(1, len(seg) - 2):
                assert seg[i + 1] == (seg[i] + 1) % C, (addr, v, s, seg)
            V2, E2, _, _ = graph(seg)
            mp = lambda x: (x[0] - s + 1, x[1])
            assert {mp(x) for x in F} == V2, ("nodes", addr, v, s)
            assert {(mp(u), mp(w)) for (u, w) in FE} == E2, ("edges", addr, v, s)
            count[0] += 1


def main():
    Cmax, Tmax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (5, 12)
    count = [0]
    for C in range(1, Cmax + 1):
        for T in range(1, Tmax + 1):
            addr = [None] + [(t - 1) % C for t in range(1, T + 1)]
            check_ladder(addr, C, count)
    n1 = count[0]
    # segments of the class with an arbitrary top (and arbitrary RR start), as foci arise after jumps
    rng = random.Random(1)
    for C in range(1, Cmax + 1):
        for T in range(1, Tmax + 1):
            for start in range(C):
                for topc in range(C):
                    addr = [None] + [(start + t - 1) % C for t in range(1, T)] + [topc]
                    check_ladder(addr, C, count)
    print(f"closure: round robin C<={Cmax}, T<={Tmax}: {n1} foci; segments with arbitrary start/top: {count[0]-n1} foci; all equal")


if __name__ == '__main__':
    main()
