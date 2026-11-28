"""Exact reversible pebbling numbers of the frame DAGs of the round-three table, compared with their frame-game values.

For every instance of the round-three table (truth_claim_frame_game.py, same families and seeds) this script
  - builds the frame DAG with truth_claim_frame_game.frame_dag;
  - computes the frame-game value with the Dymond-Tompa solver (frame_dag_dymond_tompa_value.cpp, table 2^24);
  - runs the reversible search (frame_dag_black_and_reversible_pebbling.cpp, mode rev; exhaustive over
    reversible configurations) and records Rev and RevVisit.
Chan (ECCC TR13-042, Def. 3.4-3.5, Theorem 1) counts the sink pebble: Dymond-Tompa time = 1 + (placements after
the sink); the frame value counts placements after the sink only. The prediction checked is Rev = frame value + 1.
A value written ">=L" is a lower bound only: the search stopped at its state cap or at the time limit.
Usage: python3 -I -B frame_dag_reversible_pebbling_versus_frame_value.py
           [<Tmin> <Tmax> <seconds per reversible search> <cap_log2> [seconds per frame-value search, default 60]]
With no arguments: 2 7 60 24 20.
"""
import sys, os, random, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import truth_claim_node_game as ng
import truth_claim_frame_game as fg
import frame_dag_solvers as solvers

def instances(T):
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
    return rows

def dag_text(P, tgt):
    return "%d %d\n" % (len(P), tgt) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)

def run(cmd, txt, secs):
    pr = subprocess.Popen(["nice", "-n", "19"] + cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    try:
        out, _ = pr.communicate(txt, timeout=secs)
        return out, False
    except subprocess.TimeoutExpired:
        pr.kill(); out, _ = pr.communicate(); return out, True

def parse_peb(out, timed_out):
    visit = None; fails = []
    for l in out.splitlines():
        w = l.split()
        if w[0] == 'visit': visit = int(w[1])
        if w[0] == 'fail': fails.append(int(w[1]))
        if w[0] == 'exact': return ('exact', int(w[1]), visit, w[3])
        if w[0] == 'capped': return ('lower', int(w[1]), visit, w[3])
    return ('lower', (max(fails) + 1) if fails else 1, visit, 'timeout' if timed_out else '?')

def parse_dt(out):
    fails = []
    for l in out.splitlines():
        w = l.split()
        if w[0] == 'fail': fails.append(int(w[1]))
        if w[0] == 'exact': return ('exact', int(w[1]))
        if w[0] == 'lower': return ('lower', int(w[1]))
    return ('lower', (max(fails) + 1) if fails else 0)

if __name__ == "__main__":
    args = sys.argv[1:] or ['2', '7', '60', '24', '20']
    Tmin, Tmax = int(args[0]), int(args[1])
    secs = float(args[2]); lg = args[3]
    dtsecs = float(args[4]) if len(args) > 4 else 60
    print("# name T M nodes | frame value | Rev (Chan) | RevVisit | Rev - frame value | states")
    for T in range(Tmin, Tmax + 1):
        for name, T_, M_, steps in instances(T):
            order, P, tgt = fg.frame_dag(steps)
            if len(P) > 63:
                print(name, T_, M_, len(P), '| too large', flush=True); continue
            txt = dag_text(P, tgt)
            out, to = run([solvers.binary('dt'), '40', '24'], txt, dtsecs)
            dkind, dval = parse_dt(out)
            dts = str(dval) if dkind == 'exact' else '>=%d' % dval
            out, to = run([solvers.binary('peb'), 'rev', '40', lg], txt, secs)
            kind, val, visit, states = parse_peb(out, to)
            revs = str(val) if kind == 'exact' else '>=%d' % val
            diff = str(val - dval) if kind == 'exact' and dkind == 'exact' else '-'
            print(name, T_, M_, len(P), '|', dts, '|', revs, '|', visit, '|', diff, '|', states, flush=True)
