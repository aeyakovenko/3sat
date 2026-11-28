"""Write the frame DAG of one instance of the round-three table, in the solvers' input format, to stdout.
Usage: python3 -I -B frame_dag_writer.py [<family> <T> [occurrence index 0/1 for store_heavy M=4,6 order]]
(no arguments: ladder_rr 9). For example
python3 -I -B frame_dag_writer.py ladder_rr 9 | python3 -I -B frame_dag_solvers.py peb rev 10 28 10"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import frame_dag_reversible_pebbling_versus_frame_value as yc, truth_claim_frame_game as fg
args = sys.argv[1:] or ['ladder_rr', '9']
name, T, occ = args[0], int(args[1]), int(args[2]) if len(args) > 2 else 0
rows = [r for r in yc.instances(T) if r[0] == name]
order, P, tgt = fg.frame_dag(rows[occ][3])
sys.stdout.write(yc.dag_text(P, tgt))
