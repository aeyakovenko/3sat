"""The cone-restricted bisection strategy in the frame game of the round-three truth-claim entry
(truth_claim_frame_game.py), on overwrite ladders; notes/frame-game-upper-bound-on-overwrite-ladders.md.

Strategy (block form; one-at-a-time placement is at least as good for the prover, so the
frame value is at most the block cost). Position: challenged node v at layer r, and every ancestor of v
at layer l < r pebbled (layer 0 = known initial facts). If r = l+1 the game is over (cost 0). Otherwise
pick m in (l, r), place the block A = anc(v) & layer m, and recurse:
   g(v, l) = |A| + max( g(v, m), max_{u in A} g(u, l) ).
On a ladder every edge goes from layer t-1 to layer t, so A is a cut for v's cone (stay branch), and
anc(u) & layer l is contained in anc(v) & layer l for u in A (move branch).
Closed form: |anc(v) & layer m| <= min(C, r - m + 1) (induction on r - m: every node's predecessors are
the previous state S plus at most one other node), hence with m = l + floor(L/2), L = r - l,
   g <= f(L),  f(1) = 0,  f(L) = min(C, ceil(L/2) + 1) + f(ceil(L/2)).
Modes:
  check <Tmax> <seconds> <cap_log2> : for every ladder with T <= Tmax among round-robin (C = 2..T) and
      random sequences, compares the exact frame value (frame_dag_dymond_tompa_value.cpp), the exact optimum over m of the block
      strategy (gmin), the midpoint strategy (gmid) and f(T); asserts DT <= gmin <= gmid <= f(T).
  table <C> <T1,T2,...> : round-robin ladder, midpoint strategy and f, for large T.
  scaling : f(T) at C = T/log2 T against T, (C+1)ceil(log2 T) and C*log2(T/C).
  closed <Cmax> <emax> : asserts f(T) <= C*log2(T/C) + 3C on a grid.
With no argument: closed 300 30, scaling, table 4 8,16,32,64,128,256 and table 16 32,64,128,256.
Writes nothing; the solver is built by frame_dag_solvers.py in a temporary directory.
"""
import sys, os, math, random, subprocess, functools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg
import frame_dag_solvers as solvers
sys.setrecursionlimit(100000)

def build(seq):
    order, P, tgt = fg.frame_dag(ng.ladder(seq))
    n = len(order)
    layer = [x[1] for x in order]
    anc = [0] * n
    for i in range(n):            # topological order
        a = 0
        for p in P[i]:
            a |= (1 << p) | anc[p]
        anc[i] = a
    for i in range(n):
        for p in P[i]:
            assert layer[p] == layer[i] - 1, "not layered"
    bylayer = {}
    for i in range(n):
        bylayer.setdefault(layer[i], 0)
        bylayer[layer[i]] |= 1 << i
    return order, P, tgt, layer, anc, bylayer

def bits(x):
    out = []
    while x:
        b = x & -x; out.append(b.bit_length() - 1); x ^= b
    return out

def strategy(seq, exact):
    order, P, tgt, layer, anc, bylayer = build(seq)
    @functools.lru_cache(maxsize=None)
    def g(v, l):
        r = layer[v]
        if r == l + 1:
            return 0
        ms = range(l + 1, r) if exact else [l + (r - l) // 2]
        best = None
        for m in ms:
            A = bits(anc[v] & bylayer.get(m, 0))
            val = len(A) + max([g(v, m)] + [g(u, l) for u in A])
            if best is None or val < best:
                best = val
        return best
    return g(tgt, 0), len(order), P, tgt

def width_ok(seq):
    # checks |anc(v) & layer m| <= min(C, r - m + 1) for every node v (layer r) and every m < r
    order, P, tgt, layer, anc, bylayer = build(seq)
    C = len(set(seq))
    for v in range(len(order)):
        r = layer[v]
        for m in range(1, r):
            if bin(anc[v] & bylayer.get(m, 0)).count('1') > min(C, r - m + 1):
                return False
    return True

def closed(Cmax, emax):
    # asserts f(T) <= C*log2(T/C) + 3C on the grid 2 <= C <= Cmax, T = C*2^e*q, and reports the max slack
    worst = (-1e9, None)
    for C in range(2, Cmax + 1):
        for e in range(0, emax + 1):
            for q in (1, 1.25, 1.5, 1.75):
                T = int(C * (2 ** e) * q)
                if T < C: continue
                val = (f(T, C) - C * math.log2(T / C)) / C
                assert val <= 3, (C, T, f(T, C))
                if val > worst[0]: worst = (val, (C, T, f(T, C)))
    print("closed form: max over grid of (f(T) - C*log2(T/C))/C = %.4f at (C, T, f) = %s; bound 3 holds" % worst)

def f(L, C):
    return 0 if L <= 1 else min(C, (L + 1) // 2 + 1) + f((L + 1) // 2, C)

def dag_text(P, tgt):
    return "%d %d\n" % (len(P), tgt) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)

def frame_dt(P, tgt, secs, lg):
    pr = subprocess.Popen(["nice", "-n", "19", solvers.binary("dt"), "60", str(lg)],
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    try:
        out, _ = pr.communicate(dag_text(P, tgt), timeout=secs)
    except subprocess.TimeoutExpired:
        pr.kill(); pr.communicate(); return None
    for l in out.splitlines():
        w = l.split()
        if w and w[0] == 'exact':
            return int(w[1])
    return None

def check(Tmax, secs, lg):
    rng = random.Random(7)
    bad = 0; rows = 0; tight = 0; solved = 0
    print("# kind C T nodes | DT exact | gmin | gmid | f(T)")
    for T in range(2, Tmax + 1):
        seqs = [("rr", C, ng.round_robin(T, C)) for C in range(2, T + 1)]
        for C in (2, 3, max(2, T // 3), max(2, T // 2)):
            for rep in range(2):
                seqs.append(("rand", C, [rng.randrange(C) for _ in range(T)]))
        for kind, C, seq in seqs:
            Ceff = len(set(seq))
            gmin, n, P, tgt = strategy(seq, True)
            gmid, _, _, _ = strategy(seq, False)
            dt = frame_dt(P, tgt, secs, lg) if n <= 63 else None
            fT = f(T, Ceff)
            wid = width_ok(seq)
            ok = wid and gmin <= gmid <= fT and (dt is None or dt <= gmin)
            rows += 1; bad += (not ok)
            if dt is not None:
                solved += 1; tight += (dt == gmin)
            print(kind, Ceff, T, n, "|", dt if dt is not None else "-", "|", gmin, "|", gmid, "|", fT, "" if ok else "VIOLATION", flush=True)
    print("# rows %d, DT solved %d, DT == gmin on %d, violations %d" % (rows, solved, tight, bad))

def table(C, Ts):
    print("# round-robin C=%d | T | gmid (midpoint strategy, exact count) | f(T) | (C+1)ceil(log2 T) | walk ~T" % C)
    for T in Ts:
        gmid, n, _, _ = strategy(ng.round_robin(T, C), False)
        print(C, T, "|", gmid, "|", f(T, C), "|", (C + 1) * math.ceil(math.log2(T)), "|", T, flush=True)

def scaling():
    print("# T | C = round(T/log2 T) | f(T) | f(T)/T | (C+1)ceil(log2 T) | C*log2(T/C)")
    for e in range(6, 41, 2):
        T = 2 ** e; C = max(2, round(T / math.log2(T)))
        print(T, "|", C, "|", f(T, C), "| %.4f |" % (f(T, C) / T), (C + 1) * math.ceil(math.log2(T)), "| %.0f" % (C * math.log2(T / C)))

if __name__ == "__main__":
    if len(sys.argv) == 1:
        closed(300, 30)
        scaling()
        table(4, [8, 16, 32, 64, 128, 256])
        table(16, [32, 64, 128, 256])
        sys.exit(0)
    mode = sys.argv[1]
    if mode == "check":
        check(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif mode == "table":
        table(int(sys.argv[2]), [int(x) for x in sys.argv[3].split(",")])
    elif mode == "scaling":
        scaling()
    elif mode == "closed":
        closed(int(sys.argv[2]), int(sys.argv[3]))
