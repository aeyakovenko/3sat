"""Cube-cycle catalog: pair-block variant of the sequential family (upper-bound search).

LOAD d; branch on top(d) (one comparison); then the pair (a, b) by one exhaustive
two-word tree that must report FAIL or top(b), then the pair (c, d) by one
exhaustive two-word tree (d restricted to the half given by the probe).  The
trees are found by cube_cycle_tree_search (`custom` mode): minimum over all trees of
comparisons on {x, y, literals} and at most MAX_ALU ALU instructions per path.
Prints the optimal budgets; total non-load steps = 1 + P1.

usage: python3 cube_cycle_pair_blocks.py SOLVER WORKDIR MAX_ALU [p2only]
(p2only: stop after the second-phase costs; the first phase with ALU instructions is run
separately because the budget loop would be slow)
"""
import json, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cube_cycle_native_model import SAFE
if len(sys.argv) < 4:
    sys.exit('usage: python3 cube_cycle_pair_blocks.py SOLVER WORKDIR MAX_ALU [p2only]')
SOLVER, WORK, MAX_ALU = sys.argv[1], sys.argv[2], sys.argv[3]
os.makedirs(WORK, exist_ok=True)
top = lambda w: w >> 3
low = lambda w: w & 1
ok = lambda x, y: x in SAFE and y in SAFE and (top(x) or low(y))
def solve(labels, costs, names, tag, kmin=0, kmax=12):
    path = os.path.join(WORK, f'problem_{tag}.txt')
    with open(path, 'w') as out:
        out.write(f'{len(names)}\n{" ".join(map(str, costs))}\n{" ".join(names)}\n')
        out.write(' '.join(str(v) for v in labels) + '\n')
    for k in range(kmin, kmax + 1):
        res = subprocess.run([SOLVER, 'custom', str(k), MAX_ALU, path], capture_output=True, text=True, check=True,
                             env=dict(os.environ, OMP_NUM_THREADS=os.environ.get('OMP_NUM_THREADS', '8')))
        tree = [line[5:] for line in res.stdout.splitlines() if line.startswith('TREE ')]
        if tree:
            return k, json.loads(tree[0])
    return None, None
P2 = {}
for t1 in (0, 1):
    for t3 in (0, 1):
        labels = []
        for p in range(256):
            c, d = p & 15, p >> 4
            labels.append(-1 if top(d) != t3 else int(ok(c, d) and (t1 or low(c))))
        P2[t1, t3], _ = solve(labels, [0, 0], ['FAIL', 'OK'], f'pp2_{t1}{t3}')
        print('P2', t1, t3, P2[t1, t3], flush=True)
if len(sys.argv) > 4 and sys.argv[4] == 'p2only':
    sys.exit(0)
for t3 in (0, 1):
    labels = []
    for p in range(256):
        a, b = p & 15, p >> 4
        labels.append(1 + top(b) if (ok(a, b) and (t3 or low(a))) else 0)
    k, _ = solve(labels, [0, P2[0, t3], P2[1, t3]], ['FAIL', 'T0', 'T1'], f'pp1_{t3}', kmin=max(P2[0, t3], P2[1, t3]))
    print('P1', t3, k, '-> total non-load', None if k is None else 1 + k, flush=True)
