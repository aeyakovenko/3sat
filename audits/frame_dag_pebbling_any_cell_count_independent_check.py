"""Independent check written during review: on all ladder address sequences of length T with ANY number of cells
(restricted growth strings), check Black >= C, Black <= C+1, Black <= DT+1 (DT from
frame_dag_dymond_tompa_value.cpp), and for T <= revmaxT Rev = DT+1, with the solvers of
frame_dag_pebbling_independent_check.py.
Usage: python3 -I -B frame_dag_pebbling_any_cell_count_independent_check.py [<Tmin> <Tmax> <revmaxT>]
With no arguments: 2 6 5."""
import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import frame_dag_pebbling_independent_check as rc
binary = rc.solvers.binary('dt')
Tmin, Tmax, revmaxT = map(int, sys.argv[1:4] or ['2', '6', '5'])
def rgs(T):
    def rec(pre, used):
        if len(pre) == T: yield list(pre); return
        for a in range(used + 1):
            yield from rec(pre + [a], max(used, a + 1))
    yield from rec([], 0)
ok = True
for T in range(Tmin, Tmax + 1):
    n = bad = 0; hist = {}; revc = revbad = 0; dtbad = 0
    for s in rgs(T):
        C = len(set(s)); nodes, P, tgt = rc.my_frame_dag(s)
        b = rc.black(P, tgt); d = rc.frame_dt_value(binary, P, tgt)
        n += 1; hist[b - C] = hist.get(b - C, 0) + 1
        bad += (b < C) or (b > C + 1); dtbad += d is None or b > d + 1
        if T <= revmaxT:
            r = rc.rev(P, tgt); revc += 1; revbad += r != d + 1
    ok &= bad == 0 and dtbad == 0 and revbad == 0
    print("T=%d sequences=%d hist(black-C)=%s black_vs_C_violations=%d black>DT+1=%d rev_checked=%d rev!=DT+1=%d" % (T, n, hist, bad, dtbad, revc, revbad), flush=True)
print("ALL OK" if ok else "SOMETHING FAILED")
