"""Checks of the round-robin special case of the black-pebbling lower bound.
(1) For T = 2..14, in the frame DAG of ladder_rr (M = ceil(T/2)), the ancestor cone of S_M is exactly the
    triangle D_M: nodes (a, mu), 0 <= a <= M-1, 1 <= mu <= a+1, where (a, a+1) is S_{a+1} and (a, mu) for
    mu <= a is C(mu, a); predecessors of (a, mu), mu >= 2: (a, mu-1) and S_{mu-1}.
(2) S_M is an ancestor of the sink S_T, and the DAG is layered (edges go from time sigma-1 to sigma).
Usage: python3 -I -B frame_dag_round_robin_cone_check.py"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg

def tri(M):
    def lab(a, mu):
        return ('S', mu) if mu == a + 1 else ('C', mu, a)
    nodes = {}
    for a in range(M):
        for mu in range(1, a + 2):
            ps = [] if mu == 1 else [lab(a, mu - 1), ('S', mu - 1)]
            nodes[lab(a, mu)] = set(ps)
    return nodes

ok = True
for T in range(2, 15):
    M = (T + 1) // 2
    order, P, tgt = fg.frame_dag(ng.ladder(ng.round_robin(T, M)))
    pred = {order[v]: {order[p] for p in P[v]} for v in range(len(order))}
    cone, st = set(), [('S', M)]
    while st:
        x = st.pop()
        if x in cone: continue
        cone.add(x); st.extend(pred[x])
    D = tri(M)
    same = set(D) == cone and all(pred[x] == D[x] for x in cone)
    anc_sink = True  # S_M -> S_{M+1} -> ... -> S_T along the spine
    for s in range(M + 1, T + 1):
        anc_sink &= ('S', s - 1) in pred[('S', s)]
    layered = all(order[p][1] == order[v][1] - 1 for v in range(len(P)) for p in P[v])
    print("T=%d M=%d nodes=%d cone(S_M)=%d triangle=%d equal=%s S_M ancestor of sink=%s layered=%s"
          % (T, M, len(P), len(cone), len(D), same, anc_sink, layered))
    ok &= same and anc_sink and layered
print("ALL OK" if ok else "FAILED")
