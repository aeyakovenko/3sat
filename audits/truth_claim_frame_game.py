"""Frame game of the round-three truth-claim entry (atomic truth claims, one-step checks, Dymond-Tompa rules)
on the same runs as truth_claim_node_game.py.

Claims: S_tau = state after step tau (tau >= 1; S_0 known); the cell version written at step tau is folded
into S_tau. C(tau, a) = content of cell a after step tau, for a step tau that does not write a.
One-step checks (predecessors):
  S_tau  <- S_{tau-1}, and version(a_tau, tau-1) if step tau loads;
  C(tau,a) <- version(a, tau-1), and S_{tau-1} if step tau stores at a data-dependent address
  (a load, or a store whose address is fixed by the program text, cannot write a, so needs no state).
version(a, tau) = known if tau = 0; S_tau if step tau writes a; else C(tau, a).
Only the ancestor cone of S_T is kept. The challenger has only one-bit moves (stay or move), so the
"prover pays" and "each player pays" rules coincide on this game.
Interval game (upper bound, a strategy inside the frame game): V(l,l+1)=0,
  V(l,r) = min_{l<m<r} |layer(m)| + max(V(l,m), V(m,r)), layer(m) = cone nodes at time m.
The exact values come from frame_dag_dymond_tompa_value.cpp, built by frame_dag_solvers.py.
Usage: python3 -I -B truth_claim_frame_game.py [Tmax] [per-instance seconds] [Tmin]   (defaults 8, 30, 2)
"""
import sys, os, random, subprocess, functools
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import truth_claim_node_game as ng
import frame_dag_solvers as solvers

def frame_dag(steps):
    T = len(steps)
    def writes(tau, a):
        k, ad, pub = steps[tau - 1]
        return k in ('S', 'X') and ad == a
    def version(a, tau):
        if tau == 0:
            return None
        return ('S', tau) if writes(tau, a) else ('C', tau, a)
    def preds(x):
        out = []
        if x[0] == 'S':
            tau = x[1]
            k, a, pub = steps[tau - 1]
            if tau - 1 >= 1:
                out.append(('S', tau - 1))
            if k in ('L', 'X'):
                v = version(a, tau - 1)
                if v is not None:
                    out.append(v)
        else:
            tau, a = x[1], x[2]
            k, ad, pub = steps[tau - 1]
            v = version(a, tau - 1)
            if v is not None:
                out.append(v)
            if k in ('S', 'X') and not pub and tau - 1 >= 1:
                out.append(('S', tau - 1))
        return list(dict.fromkeys(out))
    cone = set(); stack = [('S', T)]
    while stack:
        x = stack.pop()
        if x in cone:
            continue
        cone.add(x)
        stack.extend(preds(x))
    order = sorted(cone, key=lambda x: (x[1], 0 if x[0] == 'C' else 1, x[2] if x[0] == 'C' else -1))
    idx = {x: i for i, x in enumerate(order)}
    P = [[idx[p] for p in preds(x)] for x in order]
    return order, P, idx[('S', T)]

def interval_value(order, T):
    layer = [0] * (T + 1)
    for x in order:
        layer[x[1]] += 1
    @functools.lru_cache(maxsize=None)
    def V(l, r):
        if r == l + 1:
            return 0
        return min(layer[m] + max(V(l, m), V(m, r)) for m in range(l + 1, r))
    return V(0, T), max(layer[1:T]) if T > 1 else 0

def brute_dt(P, target):
    n = len(P)
    pm = [sum(1 << p for p in ps) for ps in P]
    @functools.lru_cache(maxsize=None)
    def V(c, S):
        if pm[c] & ~S == 0:
            return 0
        best = None
        for v in range(n):
            if not (S >> v) & 1:
                Q = S | (1 << v)
                val = 1 + max(V(v, Q), V(c, Q))
                if best is None or val < best:
                    best = val
        return best
    return V(target, 0)

def run_c(binary, P, target, secs):
    """Returns ('exact', v), ('lower', L) on cap abort, or ('lower', L) on timeout with L = levels proved."""
    txt = "%d %d\n" % (len(P), target) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)
    pr = subprocess.Popen(["nice", "-n", "19", binary, "40", "25"], stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, text=True)
    try:
        out, _ = pr.communicate(txt, timeout=secs)
    except subprocess.TimeoutExpired:
        pr.kill()
        out, _ = pr.communicate()
    fails = [int(l.split()[1]) for l in out.splitlines() if l.startswith("fail")]
    for l in out.splitlines():
        if l.startswith("exact"):
            return ["exact", l.split()[1]]
        if l.startswith("lower"):
            return ["lower", l.split()[1]]
    return ["lower", str(max(fails) + 1 if fails else 0)]

if __name__ == "__main__":
    binary = solvers.binary('dt')
    Tmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    secs = float(sys.argv[2]) if len(sys.argv) > 2 else 30
    Tmin = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    print("# family T M nodes | frame value (exact or [lower, interval-upper]) | interval value | max layer | node-game ruleP (pub=1)")
    for T in range(Tmin, Tmax + 1):
        rows = [("const_reader", T, 1, ng.constant_reader(T))]
        M = (T + 1) // 2
        rows.append(("ladder_rr", T, M, ng.ladder(ng.round_robin(T, M))))
        rng = random.Random(1000 + T)
        for rep in range(2):
            rows.append(("ladder_rand%d" % rep, T, M, ng.ladder(ng.random_seq(T, M, rng))))
        for M2 in (4, 6):
            rng2 = random.Random(2000 + 10 * T + M2)
            for rep in range(2):
                rows.append(("store_heavy%d" % rep, T, M2, ng.random_store_heavy(T, M2, 0.6, rng2)))
        for name, T_, M_, steps in rows:
            order, P, tgt = frame_dag(steps)
            iv, maxlayer = interval_value(order, T_)
            curve, sumv = ng.values(steps, True)
            n = len(order)
            if n > 63:
                res = "too-large"
            else:
                out = run_c(binary, P, tgt, secs)
                if out[0] == "exact":
                    v = int(out[1])
                    assert v <= iv, (name, T_, v, iv)
                    if T_ <= 5:
                        bv = brute_dt(P, tgt)
                        assert bv == v, (name, T_, bv, v)
                    res = "%d" % v
                elif out[0] == "lower":
                    res = "[%s,%d]" % (out[1], iv)
            print(name, T_, M_, n, "|", res, "|", iv, "|", maxlayer, "|", curve[T_], flush=True)
