"""Exact black (and reversible) pebbling numbers of the round-robin ladder's frame DAG.
The DAG is truth_claim_frame_game.frame_dag of ladder(round_robin(T, M)), M = ceil(T/2) (the family ladder_rr).
Also prints the column sizes (cone nodes per time step) and checks that the DAG is layered: every edge goes
from time sigma-1 to time sigma.
Usage: python3 -I -B frame_dag_round_robin_black_pebbling.py [<Tmin> <Tmax> <seconds> <cap_log2> [rev]]
With no arguments: 2 9 60 26.
"""
import sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import truth_claim_node_game as ng
import truth_claim_frame_game as fg
import frame_dag_solvers as solvers

def dag_text(P, tgt):
    return "%d %d\n" % (len(P), tgt) + "".join("%d %s\n" % (len(ps), " ".join(map(str, ps))) for ps in P)

if __name__ == "__main__":
    args = sys.argv[1:] or ['2', '9', '60', '26']
    Tmin, Tmax, secs, lg = int(args[0]), int(args[1]), float(args[2]), args[3]
    modes = ['black'] + (['rev'] if len(args) > 4 else [])
    for T in range(Tmin, Tmax + 1):
        M = (T + 1) // 2
        order, P, tgt = fg.frame_dag(ng.ladder(ng.round_robin(T, M)))
        layered = all(order[p][1] == order[v][1] - 1 for v in range(len(P)) for p in P[v])
        cols = [sum(1 for x in order if x[1] == s) for s in range(1, T + 1)]
        res = []
        for mode in modes:
            pr = subprocess.Popen(["nice", "-n", "19", solvers.binary('peb'), mode, '40', lg],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
            try:
                out, _ = pr.communicate(dag_text(P, tgt), timeout=secs)
            except subprocess.TimeoutExpired:
                pr.kill(); out, _ = pr.communicate()
            last = out.strip().splitlines()[-1] if out.strip() else 'none'
            res.append("%s: %s" % (mode, last))
        print("T=%d M=%d nodes=%d layered=%s columns=%s | %s" % (T, M, len(P), layered, cols, " | ".join(res)), flush=True)
