"""Independent check, written during review, of Proposition 2 of notes/frame-game-upper-bound-on-overwrite-ladders.md
(independent of frame_game_cone_bisection.py). Uses the journal's frame-DAG builder (truth_claim_frame_game.py) and
DT solver (frame_dag_dymond_tompa_value.cpp, built by frame_dag_solvers.py in a temporary directory).

sim(): plays the cone-restricted bisection in ONE-AT-A-TIME form under the journal's game rules: position
(c, P) with P the true pebble set restricted to anc(c); prover places one node; challenger stays or moves to it;
position is won when preds(c) are all pebbled.  Strategy state (v, l): before each block the script ASSERTS
the invariant anc(v) & layer l is pebbled (l = 0 means known facts), and at r - l = 1 ASSERTS the game is over.
Returns the worst case number of placements over all challenger choices (memo on (v, l, P & anc(v))).
Also checks Lemma 1 (|anc(v) & layer m| <= min(C, r-m+1)) and computes the journal's interval-game value.
Modes: exact SEED TMAX SECONDS | other SEED TMAX SECONDS | big SEED C,T [C,T ...]
  (no argument: big 11 2,24 2,64 3,48 4,64 4,256 8,64 8,256, the review's run without its three largest ladders).
  Writes nothing.
"""
import sys, os, random, subprocess, functools, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_frame_game as fg, truth_claim_node_game as ng
import frame_dag_solvers as solvers
sys.setrecursionlimit(1000000)

def f(L, C):
    return 0 if L <= 1 else min(C, -(-L // 2) + 1) + f(-(-L // 2), C)

def analyse(steps, want_dt=False, secs=30, lg=24, extra=0):
    order, P, tgt = fg.frame_dag(steps)
    n = len(order); layer = [x[1] for x in order]
    pred = [frozenset(ps) for ps in P]
    anc = [None] * n
    for i in range(n):
        s = set()
        for p in P[i]:
            s.add(p); s |= anc[p]
        anc[i] = frozenset(s)
    for i in range(n):
        for p in P[i]:
            assert layer[p] == layer[i] - 1
    T = layer[tgt]
    cells = set(x[2] for x in order if x[0] == 'C') | set(a for (_, a, _) in steps)
    C = len(set(a for (_, a, _) in steps)) + extra
    bylayer = {}
    for i in range(n):
        bylayer.setdefault(layer[i], set()).add(i)
    # Lemma 1
    for v in range(n):
        r = layer[v]
        for m in range(1, r):
            w = len(anc[v] & bylayer.get(m, set()))
            assert w <= min(C, r - m + 1), ("Lemma1", v, m, w)
    @functools.lru_cache(maxsize=None)
    def sim(v, l, Pv):
        Pv = set(Pv)
        r = layer[v]
        if l >= 1:
            assert (anc[v] & bylayer[l]) <= Pv, "invariant broken"
        if pred[v] <= Pv:
            return 0
        L = r - l
        assert L >= 2, "L=1 but game not over"
        m = l + L // 2
        A = sorted(anc[v] & bylayer[m])
        cost = 0; worst = 0
        for u in A:
            if u in Pv:
                continue
            Pv.add(u); cost += 1
            worst = max(worst, cost + sim(u, l, frozenset(Pv & anc[u])))   # challenger moves to u
            if pred[v] <= Pv:                                               # challenger stays: game over
                return max(worst, cost)
        return max(worst, cost + sim(v, m, frozenset(Pv & anc[v])))        # challenger stayed throughout
    s = sim(tgt, 0, frozenset())
    iv, _ = fg.interval_value(order, T)
    dt = None
    if want_dt and n <= 63:
        txt = "%d %d\n" % (n, tgt) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)
        try:
            out = subprocess.run(["nice", "-n", "19", solvers.binary("dt"), "60", str(lg)], input=txt, capture_output=True,
                                 text=True, timeout=secs).stdout
            for line in out.splitlines():
                if line.startswith("exact"):
                    dt = int(line.split()[1])
        except subprocess.TimeoutExpired:
            dt = None
    return dict(n=n, T=T, C=C, sim=s, f=f(T, C), iv=iv, dt=dt)

if __name__ == "__main__":
    if len(sys.argv) == 1:
        sys.argv += ["big", "11", "2,24", "2,64", "3,48", "4,64", "4,256", "8,64", "8,256"]
    mode = sys.argv[1]
    if mode == "exact":          # sample vs journal DT solver
        rng = random.Random(int(sys.argv[2])); Tmax = int(sys.argv[3]); secs = float(sys.argv[4])
        bad = 0; rows = 0; solved = 0
        print("# kind C T n | DT(journal) | sim | f_C(T) | interval")
        for T in range(2, Tmax + 1):
            seqs = []
            for C in range(2, T + 1):
                seqs.append(("rr", ng.round_robin(T, C)))
            for rep in range(3):
                C = rng.randrange(2, T + 1)
                seqs.append(("rand", [rng.randrange(C) for _ in range(T)]))
            for kind, seq in seqs:
                d = analyse(ng.ladder(seq), True, secs)
                ok = d['sim'] <= d['f'] and (d['dt'] is None or d['dt'] <= d['sim'])
                rows += 1; bad += not ok; solved += d['dt'] is not None
                print(kind, d['C'], T, d['n'], "|", d['dt'] if d['dt'] is not None else "-", "|", d['sim'], "|",
                      d['f'], "|", d['iv'], "" if ok else "VIOLATION", flush=True)
        print("# rows %d solved %d violations %d" % (rows, solved, bad))
    elif mode == "other":        # Remark: runs with L / S / X steps, bound f_{C+1}(T); Lemma 1 with C+1
        rng = random.Random(int(sys.argv[2])); Tmax = int(sys.argv[3]); secs = float(sys.argv[4]); bad = 0; rows = 0; solved = 0
        for T in range(2, Tmax + 1):
            runs = [("const_reader", ng.constant_reader(T))]
            for M in (2, 4, 6):
                runs.append(("store_heavy", ng.random_store_heavy(T, M, 0.6, rng)))
                runs.append(("mixed", [(rng.choice("LSX"), rng.randrange(M), rng.random() < 0.3) for _ in range(T)]))
            for kind, steps in runs:
                d = analyse(steps, True, secs, 24, 1)
                ok = d['sim'] <= d['f'] and (d['dt'] is None or d['dt'] <= d['sim'])
                rows += 1; bad += not ok; solved += d['dt'] is not None
                if not ok or T >= Tmax - 1: print(kind, "C+1=%d" % d['C'], T, d['n'], "|", d['dt'], "|", d['sim'], "|", d['f'], "" if ok else "VIOLATION", flush=True)
        print("# rows %d solved %d violations %d" % (rows, solved, bad))
    elif mode == "big":          # strategy simulation only, larger T
        rng = random.Random(int(sys.argv[2]))
        bad = 0
        for spec in sys.argv[3:]:
            C, T = map(int, spec.split(","))
            for kind, seq in (("rr", ng.round_robin(T, C)), ("rand", [rng.randrange(C) for _ in range(T)])):
                d = analyse(ng.ladder(seq))
                ok = d['sim'] <= d['f']
                bad += not ok
                print(kind, d['C'], T, d['n'], "| sim", d['sim'], "| f", d['f'], "| interval", d['iv'],
                      "| C*log2(T/C)+2C+2log2C+2 = %.1f" % (d['C'] * math.log2(T / d['C']) + 2 * d['C'] + 2 * math.log2(d['C']) + 2),
                      "" if ok else "VIOLATION", flush=True)
        print("# violations", bad)
