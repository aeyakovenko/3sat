"""Black and reversible pebbling numbers of the first-round triangle: the frame DAG (truth_claim_frame_game.frame_dag)
of the ladder with address sequence 0,1,...,L-1 (every step reads a cell never written before). Usage:
python3 -I -B frame_dag_first_round_triangle_pebbling.py [<Lmin> <Lmax> <seconds> <cap_log2>]
With no arguments: 1 7 40 25."""
import sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg, frame_dag_solvers as solvers
import frame_dag_reversible_pebbling_versus_frame_value as yc
args = sys.argv[1:] or ['1', '7', '40', '25']
Lmin, Lmax, secs, lg = int(args[0]), int(args[1]), float(args[2]), args[3]
for L in range(Lmin, Lmax + 1):
    order, P, tgt = fg.frame_dag(ng.ladder(list(range(L))))
    res = []
    for mode in ('black', 'rev'):
        pr = subprocess.Popen(["nice", "-n", "19", solvers.binary('peb'), mode, '40', lg],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        try:
            out, _ = pr.communicate(yc.dag_text(P, tgt), timeout=secs)
        except subprocess.TimeoutExpired:
            pr.kill(); out, _ = pr.communicate()
        res.append("%s: %s" % (mode, out.strip().splitlines()[-1] if out.strip() else 'none'))
    print("L=%d nodes=%d | %s" % (L, len(P), " | ".join(res)), flush=True)
