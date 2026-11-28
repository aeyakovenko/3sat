"""Independent check of the frame-DAG pebbling bounds, written during review from the definitions, not from the
note's scripts.
- my_frame_dag(seq): frame DAG of the overwrite ladder (every step X at data-dependent address),
  built from the stated rules; compared node-for-node and edge-for-edge with truth_claim_frame_game.frame_dag.
- black(G), rev(G): BFS over configurations, own implementation.
- dt(G): the frame game's Dymond-Tompa rules (challenged node starts unpebbled, cost = placements), own minimax,
  compared with frame_dag_dymond_tompa_value.cpp (DT below) for T <= dtmaxT.
Checks, on all ladder sequences with at most M = ceil(T/2) cells: Black >= C (C = distinct cells), Black <= C+1,
Black <= DT+1, and for T <= revmaxT Rev = DT+1. The spine-run claim itself is not checked numerically
(Black >= C is its consequence).
Usage: python3 -I -B frame_dag_pebbling_independent_check.py [<Tmin> <Tmax> <dtmaxT> <revmaxT>]
With no arguments: 2 6 6 6.
"""
import sys, os, subprocess, itertools
from collections import deque
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frame_dag_solvers as solvers

def my_frame_dag(seq):
    T = len(seq)
    def version(a, s):  # node representing cell a after step s (None = initial, known)
        if s == 0: return None
        return ('S', s) if seq[s-1] == a else ('C', s, a)
    def preds(x):
        if x[0] == 'S':
            t = x[1]; out = []
            if t >= 2: out.append(('S', t-1))
            v = version(seq[t-1], t-1)
            if v is not None: out.append(v)
            return out
        s, a = x[1], x[2]; out = []
        v = version(a, s-1)
        if v is not None: out.append(v)
        if s >= 2: out.append(('S', s-1))
        return out
    cone = set(); st = [('S', T)]
    while st:
        x = st.pop()
        if x in cone: continue
        cone.add(x); st.extend(preds(x))
    nodes = sorted(cone, key=lambda x: (x[1], x[0] == 'S', x[2] if x[0] == 'C' else -1))
    idx = {x: i for i, x in enumerate(nodes)}
    P = [sorted(idx[p] for p in set(preds(x))) for x in nodes]
    return nodes, P, idx[('S', T)]

def masks(P):
    return [sum(1 << p for p in ps) for ps in P]

def black(P, tgt):
    n = len(P); pm = masks(P)
    for s in range(1, n + 1):
        seen = {0}; dq = deque([0])
        while dq:
            X = dq.popleft(); c = bin(X).count('1')
            for v in range(n):
                b = 1 << v
                if X & b: Y = X & ~b
                else:
                    if c >= s or pm[v] & ~X: continue
                    Y = X | b
                    if v == tgt: return s
                if Y not in seen: seen.add(Y); dq.append(Y)
    return None

def rev(P, tgt):
    n = len(P); pm = masks(P); goal = 1 << tgt
    for s in range(1, n + 1):
        seen = {0}; dq = deque([0])
        while dq:
            X = dq.popleft(); c = bin(X).count('1')
            for v in range(n):
                b = 1 << v
                if pm[v] & ~X: continue
                if X & b: Y = X & ~b
                else:
                    if c >= s: continue
                    Y = X | b
                if Y == goal: return s
                if Y not in seen: seen.add(Y); dq.append(Y)
    return None

def dt(P, tgt):
    n = len(P); pm = masks(P)
    anc = [0] * n
    for i in range(n):
        a = pm[i]
        for j in range(n):
            if pm[i] >> j & 1: a |= anc[j]
        anc[i] = a
    sys.setrecursionlimit(100000)
    memo = {}
    def V(c, X):
        X &= anc[c]
        if pm[c] & ~X == 0: return 0
        key = (c, X)
        if key in memo: return memo[key]
        best = 10**9
        cand = anc[c] & ~X
        for v in range(n):
            if cand >> v & 1:
                Y = X | (1 << v)
                a = V(c, Y)
                if 1 + a >= best: continue
                b = V(v, Y)
                val = 1 + max(a, b)
                if val < best: best = val
        memo[key] = best
        return best
    return V(tgt, 0)

def seqs(T, M):
    def rec(pre, used):
        if len(pre) == T: yield list(pre); return
        for a in range(min(used + 1, M)):
            yield from rec(pre + [a], max(used, a + 1))
    yield from rec([], 0)

def frame_dt_value(binary, P, tgt):
    txt = "%d %d\n" % (len(P), tgt) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)
    out = subprocess.run(["nice", "-n", "19", binary, "40", "24"], input=txt, capture_output=True, text=True).stdout
    for l in out.splitlines():
        if l.startswith("exact"): return int(l.split()[1])
    return None

if __name__ == "__main__":
    binary = solvers.binary('dt')
    Tmin, Tmax, dtmaxT, revmaxT = map(int, sys.argv[1:5] or ['2', '6', '6', '6'])
    import truth_claim_node_game as ng, truth_claim_frame_game as fg
    allok = True
    for T in range(Tmin, Tmax + 1):
        M = (T + 1) // 2
        stats = dict(n=0, dag_mismatch=0, bl_lt_C=0, bl_gt_C1=0, hist={}, bl_gt_dt1=0, dt_mismatch_c=0,
                     rev_ne_dt1=0, revchecked=0, dtchecked=0)
        for s in seqs(T, M):
            stats['n'] += 1
            C = len(set(s))
            nodes, P, tgt = my_frame_dag(s)
            o2, P2, t2 = fg.frame_dag(ng.ladder(s))
            # compare DAGs by labels
            lab2 = [(x[0], x[1], x[2]) if x[0] == 'C' else (x[0], x[1]) for x in o2]
            e1 = {(nodes[i], tuple(sorted(nodes[p] for p in P[i]))) for i in range(len(nodes))}
            e2 = {(lab2[i], tuple(sorted(lab2[p] for p in P2[i]))) for i in range(len(lab2))}
            if e1 != e2 or nodes[tgt] != lab2[t2]:
                stats['dag_mismatch'] += 1
            b = black(P, tgt)
            stats['hist'][b - C] = stats['hist'].get(b - C, 0) + 1
            stats['bl_lt_C'] += b < C
            stats['bl_gt_C1'] += b > C + 1
            d = frame_dt_value(binary, P, tgt)
            if T <= dtmaxT:
                d2 = dt(P, tgt); stats['dtchecked'] += 1
                if d2 != d: stats['dt_mismatch_c'] += 1
            stats['bl_gt_dt1'] += b > d + 1
            if T <= revmaxT:
                r = rev(P, tgt); stats['revchecked'] += 1
                stats['rev_ne_dt1'] += r != d + 1
        bad = stats['dag_mismatch'] + stats['bl_lt_C'] + stats['bl_gt_C1'] + stats['bl_gt_dt1'] + stats['dt_mismatch_c'] + stats['rev_ne_dt1']
        allok &= bad == 0
        print("T=%d M=%d" % (T, M), stats, flush=True)
    print("ALL OK" if allok else "SOMETHING FAILED")
