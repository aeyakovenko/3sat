"""Exact Dymond-Tompa values (= Rev - 1, Chan's Theorem 1 with the off-by-one of the frame-game lower-bound
note) of the frame DAG of the round-robin overwrite ladder with C cells and T steps (a_tau = (tau-1) mod C), for
fixed C and a range of T; notes/frame-game-upper-bound-on-overwrite-ladders.md. DAG built by truth_claim_frame_game.frame_dag; solvers
frame_dag_dymond_tompa_value.cpp and/or frame_dag_black_and_reversible_pebbling.cpp, built by frame_dag_solvers.py.
Usage: python3 -I -B frame_game_round_robin_exact_values.py <C> <Tmin> <Tmax> <seconds per run> <cap_log2> [dt|rev|both]
  (no argument: 2 2 12 60 24 both)
Output per T: C T nodes | DT value (frame_dt) | Rev (peb) | bisection bound (C+1)*ceil(log2 T) | walk T-1+D
"""
import sys, os, subprocess, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg
import frame_dag_solvers as solvers

def dag_text(P, tgt):
    return "%d %d\n" % (len(P), tgt) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)

def run(cmd, txt, secs):
    pr = subprocess.Popen(["nice", "-n", "19"] + cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    try:
        out, _ = pr.communicate(txt, timeout=secs); return out, False
    except subprocess.TimeoutExpired:
        pr.kill(); out, _ = pr.communicate(); return out, True

def parse(out, to):
    last_fail = 0; res = None
    for l in out.splitlines():
        w = l.split()
        if w and w[0] == 'fail': last_fail = int(w[1])
        if w and w[0] in ('exact', 'lower', 'capped'): res = (w[0], int(w[1]))
    if res and res[0] == 'exact': return str(res[1])
    lo = last_fail + 1
    if res and res[0] in ('lower', 'capped'): lo = max(lo, res[1] if res[0] == 'lower' else res[1])
    return ">=%d%s" % (lo, " (timeout)" if to else " (cap)")

def main():
    args = sys.argv[1:] or ['2', '2', '12', '60', '24', 'both']
    C, Tmin, Tmax, secs, lg = map(int, args[:5])
    mode = args[5] if len(args) > 5 else 'dt'
    print("# C T nodes | DT(frame_dt) | Rev(peb) | bisect (C+1)ceil(log2 T) | T")
    for T in range(Tmin, Tmax + 1):
        order, P, tgt = fg.frame_dag(ng.ladder(ng.round_robin(T, C)))
        if len(P) > 63:
            print(C, T, len(P), "| too many nodes"); break
        txt = dag_text(P, tgt)
        dt = rv = '-'
        if mode in ('dt', 'both'):
            out, to = run([solvers.binary('dt'), '60', str(lg)], txt, secs); dt = parse(out, to)
        if mode in ('rev', 'both'):
            out, to = run([solvers.binary('peb'), 'rev', '60', str(lg)], txt, secs); rv = parse(out, to)
        print(C, T, len(P), "|", dt, "|", rv, "|", (C + 1) * math.ceil(math.log2(T)) if T > 1 else 0, "|", T, flush=True)

main()
