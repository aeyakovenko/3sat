#!/usr/bin/env python3
"""Claim 1 of notes/frame-value-on-round-robin-ladders.md (closure of the class of foci), checked by direct DAG
comparison with frame_dag of truth_claim_frame_game.py.

For the round-robin ladder (C, T), with G = frame_dag(ladder):
 (b) for every node v (state or column claim) at layer sigma and every s <= sigma, the nodes of
     anc(v) + {v} in layers >= s, with edges restricted to that set, are isomorphic (by the layer shift
     tau -> tau - s + 1, cells fixed, v -> top state) to frame_dag of the segment a_s .. a_{sigma-1}, cell(v);
 (a) is the special case v = S_T (the stay focus: layers >= b+1 of the cone form the suffix's frame DAG),
     and nested foci (s > 1 with a column-claim top) are covered by the same loop.
Run from audits/: python3 frame_game_focus_closure_check.py [Cmax Tmax]   (default 5 14, 6504 foci). Nothing is written.
"""
import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import truth_claim_frame_game as fg


def ladder(addrs):
    return [('X', a, False) for a in addrs]


def check(C, T):
    addrs = [(t - 1) % C for t in range(1, T + 1)]
    order, P, tgt = fg.frame_dag(ladder(addrs))
    idx = {x: i for i, x in enumerate(order)}
    preds = {x: {order[j] for j in P[i]} for i, x in enumerate(order)}
    anc = {}
    for x in order:  # topological order (by layer)
        a = set()
        for p in preds[x]:
            a |= anc[p] | {p}
        anc[x] = a
    cell = lambda x: x[2] if x[0] == 'C' else addrs[x[1] - 1]
    n_checked = 0
    for v in order:
        sig = v[1]
        for s in range(1, sig + 1):
            S = {x for x in anc[v] | {v} if x[1] >= s}
            seg = addrs[s - 1:sig - 1] + [cell(v)]
            o2, P2, t2 = fg.frame_dag(ladder(seg))
            preds2 = {x: {o2[j] for j in P2[i]} for i, x in enumerate(o2)}

            def mp(x):
                if x == v:
                    return ('S', sig - s + 1)
                if x[0] == 'S':
                    return ('S', x[1] - s + 1)
                return ('C', x[1] - s + 1, x[2])
            img = {mp(x) for x in S}
            assert len(img) == len(S), (C, T, v, s, 'not injective')
            assert img == set(o2), (C, T, v, s, 'node sets differ', sorted(img ^ set(o2)))
            for x in S:
                e1 = {mp(p) for p in preds[x] if p in S}
                assert e1 == preds2[mp(x)], (C, T, v, s, x, e1, preds2[mp(x)])
            assert mp(v) == o2[t2]
            n_checked += 1
    return n_checked


if __name__ == '__main__':
    Cmax, Tmax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (5, 14)
    tot = 0
    for C in range(1, Cmax + 1):
        for T in range(1, Tmax + 1):
            tot += check(C, T)
    print(f"closure check: C<={Cmax}, T<={Tmax}: {tot} (node, s) foci compared with frame_dag of the top-modified segment; all isomorphic")
