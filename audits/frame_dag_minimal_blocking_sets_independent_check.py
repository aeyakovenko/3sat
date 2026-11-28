"""Independent check, written during review, of Lemma 5 of notes/frame-game-upper-bound-on-overwrite-ladders.md.
Compiles frame_dag_minimal_blocking_sets_independent.cpp into a temporary directory (with $CXX, or c++), builds the
journal's frame DAG (truth_claim_frame_game.frame_dag) for round-robin and random ladders, labels each node with its
column (cell): S_t -> a_t, C(t, a) -> a, and pipes it to the checker.
Usage: python3 -I -B frame_dag_minimal_blocking_sets_independent_check.py [NMAX SEED NRANDOM]   (no argument: 24 99 40,
the review's run: 9 round-robin and 40 random ladders with at most 24 nodes, about 2 s)
Writes nothing outside the temporary directory.
"""
import sys, os, random, subprocess, tempfile, atexit, shutil
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.dont_write_bytecode = True
import truth_claim_frame_game as fg, truth_claim_node_game as ng
TEMP = tempfile.mkdtemp(prefix='minimal_blocking_sets_')
atexit.register(shutil.rmtree, TEMP, True)
BIN = os.path.join(TEMP, 'checker')
subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-w', '-o', BIN,
                os.path.join(HERE, 'frame_dag_minimal_blocking_sets_independent.cpp')], check=True)

def run(seq, tag, nmax):
    order, P, tgt = fg.frame_dag(ng.ladder(seq))
    n = len(order)
    if n > nmax:
        print(tag, seq, "skipped n=%d" % n); return
    lines = ["%d %d %d" % (n, tgt, len(seq))]
    for i, x in enumerate(order):
        colm = seq[x[1] - 1] if x[0] == 'S' else x[2]
        lines.append("%d %d %d %s" % (x[1], colm, len(P[i]), " ".join(map(str, P[i]))))
    lines.append(" ".join(map(str, seq)))
    out = subprocess.run(["nice", "-n", "19", BIN], input="\n".join(lines) + "\n", capture_output=True, text=True).stdout
    print(tag, "C=%d T=%d" % (len(set(seq)), len(seq)), seq, out.strip(), flush=True)

if __name__ == "__main__":
    args = sys.argv[1:] or ['24', '99', '40']
    nmax = int(args[0]); seed = int(args[1]); nrand = int(args[2])
    for C, T in [(2, 6), (2, 9), (3, 6), (3, 7), (4, 6), (5, 6), (2, 11), (3, 8), (4, 7)]:
        run(ng.round_robin(T, C), "rr", nmax)
    rng = random.Random(seed)
    k = 0
    while k < nrand:
        T = rng.randrange(3, 9); C = rng.randrange(2, 5)
        seq = [rng.randrange(C) for _ in range(T)]
        order, P, tgt = fg.frame_dag(ng.ladder(seq))
        if len(order) > nmax:
            continue
        run(seq, "rand", nmax); k += 1
