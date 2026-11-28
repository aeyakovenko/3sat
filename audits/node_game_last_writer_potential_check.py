"""Finite check of the node-game potential bound (truth_claim_node_game.py, rule P): on every overwrite-ladder run,
node value >= (T-1) - max(Pstar-1, 0), where Pstar = max over steps c of the last writer p(c) of the cell loaded
at c (0 if never written). Uses truth_claim_node_game's last_writer_structure and make_solver,
value V(T, {0,T}, b=T) with cost cc=0 (rule P). All ladder sequences with at most M = ceil(T/2) cells, relabelled by
first occurrence, T = Tmin..Tmax, both PUB settings; then ladder_rr and all-distinct sequences for T = 2..12.
Usage: python3 -I -B node_game_last_writer_potential_check.py [<Tmin> <Tmax>]   (no arguments: 2 7)"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_node_game as ng

def seqs(T, M):
    def rec(pre, used):
        if len(pre) == T:
            yield list(pre); return
        for a in range(min(used + 1, M)):
            yield from rec(pre + [a], max(used, a + 1))
    yield from rec([], 0)

def pstar(s):
    last, best = {}, 0
    for i, a in enumerate(s, 1):
        best = max(best, last.get(a, 0)); last[a] = i
    return best

args = sys.argv[1:] or ['2', '7']
Tmin, Tmax = int(args[0]), int(args[1])
ok = True
for T in range(Tmin, Tmax + 1):
    M = (T + 1) // 2
    for pub in (True, False):
        cnt = viol = tight = 0
        for s in seqs(T, M):
            steps = ng.ladder(s)
            hard, R = ng.last_writer_structure(steps, pub)
            V = ng.make_solver(T, hard, R, 0)
            val = V(T, 1 | (1 << T), T)
            bound = (T - 1) - max(pstar(s) - 1, 0)
            cnt += 1; viol += val < bound; tight += val == bound
        print("T=%d M=%d PUB=%s sequences=%d violations=%d tight=%d" % (T, M, pub, cnt, viol, tight), flush=True)
        ok &= viol == 0
# round-robin and all-distinct sequences, larger T
for T in range(2, 13):
    for name, s in (("ladder_rr", ng.round_robin(T, (T + 1) // 2)), ("all_distinct", list(range(T)))):
        steps = ng.ladder(s)
        hard, R = ng.last_writer_structure(steps, True)
        val = ng.make_solver(T, hard, R, 0)(T, 1 | (1 << T), T)
        bound = (T - 1) - max(pstar(s) - 1, 0)
        print("%s T=%d node value=%d bound=%d" % (name, T, val, bound), flush=True)
        ok &= val >= bound
print("ALL OK" if ok else "VIOLATION")
