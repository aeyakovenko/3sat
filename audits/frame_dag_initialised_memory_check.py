"""Check on the scope of the black-pebbling lower bound: initialise every cell by a public store first, so that no
load reads a never-stored cell, then run the round-robin ladder for R rounds. Prints the exact black pebbling number
of the frame DAG (cone of the last state). Usage: python3 -I -B frame_dag_initialised_memory_check.py [<Mmax>]
(no argument: 5)"""
import sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg, frame_dag_solvers as solvers
import frame_dag_reversible_pebbling_versus_frame_value as yc
for M in range(2, int((sys.argv[1:] or ['5'])[0]) + 1):
    for R in (1, 2):
        steps = [('S', a, True) for a in range(M)] + ng.ladder(ng.round_robin(R * M, M))
        order, P, tgt = fg.frame_dag(steps)
        if len(P) > 63:
            print("M=%d rounds=%d nodes=%d too large" % (M, R, len(P))); continue
        out = subprocess.run(["nice", "-n", "19", solvers.binary('peb'), 'black', '40', '26'],
                             input=yc.dag_text(P, tgt), capture_output=True, text=True, timeout=300).stdout
        print("M=%d rounds=%d T=%d nodes=%d black: %s" % (M, R, len(steps), len(P), out.strip().splitlines()[-1]), flush=True)
