"""Finite check of Black >= C: on the overwrite ladder (every step a load-then-store at a data-dependent
address), the black pebbling number of the frame DAG is >= k, where k = number of steps whose address was never
accessed before (on the ladder, k = C, the number of distinct cells). All address sequences with at most
M = ceil(T/2) cells, cells relabelled by first occurrence, T = Tmin..Tmax. Prints the histogram of Black - k.
Usage: python3 -I -B frame_dag_black_pebbling_at_least_cells_check.py [<Tmin> <Tmax>]   (no arguments: 2 7)"""
import sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng, truth_claim_frame_game as fg, frame_dag_solvers as solvers
import frame_dag_reversible_pebbling_versus_frame_value as yc

def seqs(T, M):
    def rec(pre, used):
        if len(pre) == T:
            yield list(pre); return
        for a in range(min(used + 1, M)):
            yield from rec(pre + [a], max(used, a + 1))
    yield from rec([], 0)

args = sys.argv[1:] or ['2', '7']
Tmin, Tmax = int(args[0]), int(args[1])
allok = True
for T in range(Tmin, Tmax + 1):
    M = (T + 1) // 2
    cnt = viol = 0; slack = {}
    for s in seqs(T, M):
        k = len(set(s))  # with relabelling by first occurrence, each new cell is a read of an untouched cell
        order, P, tgt = fg.frame_dag(ng.ladder(s))
        out = subprocess.run(["nice", "-n", "19", solvers.binary('peb'), 'black', '40', '22'],
                             input=yc.dag_text(P, tgt), capture_output=True, text=True).stdout
        b = int([l for l in out.splitlines() if l.startswith('exact')][0].split()[1])
        cnt += 1; viol += b < k; slack[b - k] = slack.get(b - k, 0) + 1
    print("T=%d M=%d sequences=%d violations(black<k)=%d  histogram of black-k: %s" % (T, M, cnt, viol, dict(sorted(slack.items()))), flush=True)
    allok &= viol == 0
print("ALL OK" if allok else "VIOLATION")
