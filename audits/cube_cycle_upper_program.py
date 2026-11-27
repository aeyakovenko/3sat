"""Cube-cycle catalog: explicit programs for the cube-cycle catalog (upper bounds).

Sequential family.  Words a, b, c, d sit at addresses 0..3.  The cover condition
is: every word is SAFE (no two adjacent zero bits inside the word) and for
every cyclically adjacent pair x -> y, top(x) = 1 or low(y) = 1.

  variant "probe":  LOAD d; branch on top(d);        (1 comparison)
                    then a, b, c one after the other, each by a single-word tree
                    that knows whether its low bit is required (top of the
                    previous word = 0) and reports FAIL or its own top bit;
                    finally d again, knowing top(d) and top(c).
  variant "state":  a first, by a single-word tree that reports (top, low);
                    then b, c as above; finally d knowing top(c) and low(a).

Every single-word tree is found by exhaustive search (cube_cycle_tree_search,
`custom ... single`): minimum over all trees of comparisons and ALU
instructions on that word of the worst value of (depth + continuation cost).
The assembled program is then run on all 65,536 inputs by the independent
interpreter of cube_cycle_native_model.py.

usage: python3 cube_cycle_upper_program.py SOLVER WORKDIR [max_alu]
"""

import json
import os
import subprocess
import sys

from cube_cycle_native_model import SAFE, evaluate

if len(sys.argv) < 3:
    sys.exit('usage: python3 cube_cycle_upper_program.py SOLVER WORKDIR [max_alu]')
SOLVER, WORK = sys.argv[1], sys.argv[2]
MAX_ALU = int(sys.argv[3]) if len(sys.argv) > 3 else 1
os.makedirs(WORK, exist_ok=True)
calls = 0


def solve_single(labels, costs, names, tag):
    """labels: 16 entries (index of a name, or -1 outside the domain).  Returns (K, tree)."""
    global calls
    path = os.path.join(WORK, f'problem_{tag}.txt')
    with open(path, 'w') as out:
        out.write(f'{len(names)}\n{" ".join(map(str, costs))}\n{" ".join(names)}\n')
        out.write(' '.join(str(labels[p & 15]) for p in range(256)) + '\n')
    for k in range(0, 12):
        calls += 1
        res = subprocess.run([SOLVER, 'custom', str(k), str(MAX_ALU), path, 'single'],
                             capture_output=True, text=True, check=True,
                             env=dict(os.environ, OMP_NUM_THREADS='8'))
        tree = [line[5:] for line in res.stdout.splitlines() if line.startswith('TREE ')]
        if tree:
            return k, json.loads(tree[0])
    raise RuntimeError('no tree found')


def top(w):
    return w >> 3


def low(w):
    return w & 1


def instantiate(tree, reg, prefix, leaves):
    """Rename x -> reg, tK -> prefix_tK, and replace leaf names by program nodes."""
    if isinstance(tree, str):
        return leaves[tree]

    def ren(x):
        if isinstance(x, int):
            return x
        return reg if x == 'x' else f'{prefix}_{x}'

    if tree['op'] == 'br':
        return {'op': 'br', 'cmp': tree['cmp'], 'a': ren(tree['a']), 'b': ren(tree['b']),
                'then': instantiate(tree['then'], reg, prefix, leaves),
                'else': instantiate(tree['else'], reg, prefix, leaves)}
    return {'op': tree['op'], 'dst': ren(tree['dst']), 'a': ren(tree['a']), 'b': ren(tree['b']),
            'next': instantiate(tree['next'], reg, prefix, leaves)}


def build_probe():
    """Returns (non-load steps on the worst path, program)."""
    V4, T4 = {}, {}
    for t2 in (0, 1):
        for t3 in (0, 1):
            labels = [(-1 if top(w) != t3 else int(w in SAFE and (t2 or low(w)))) for w in range(16)]
            V4[t2, t3], T4[t2, t3] = solve_single(labels, [0, 0], ['FAIL', 'OK'], f'p4_{t2}{t3}')

    def stage(nextcost, name):
        V, T = {}, {}
        for tprev in (0, 1):
            for t3 in (0, 1):
                labels = [(1 + top(w) if (w in SAFE and (tprev or low(w))) else 0) for w in range(16)]
                costs = [0, nextcost[0, t3], nextcost[1, t3]]
                V[tprev, t3], T[tprev, t3] = solve_single(labels, costs, ['FAIL', 'T0', 'T1'], f'{name}_{tprev}{t3}')
        return V, T

    V3, T3 = stage(V4, 'p3')
    V2, T2 = stage(V3, 'p2')
    V1, T1 = {}, {}
    for t3 in (0, 1):
        labels = [(1 + top(w) if (w in SAFE and (t3 or low(w))) else 0) for w in range(16)]
        V1[t3], T1[t3] = solve_single(labels, [0, V2[0, t3], V2[1, t3]], ['FAIL', 'T0', 'T1'], f'p1_{t3}')
    worst = 1 + max(V1.values())
    print('probe variant: V4', V4, 'V3', V3, 'V2', V2, 'V1', V1, '-> worst non-load steps', worst)

    def fin(t2, t3):
        return instantiate(T4[t2, t3], 'd', f'd{t2}{t3}', {'FAIL': 'ACCEPT', 'OK': 'REJECT'})

    def sc(t1, t3):
        return {'op': 'load', 'dst': 'c', 'addr': 2, 'next': instantiate(
            T3[t1, t3], 'c', f'c{t1}{t3}', {'FAIL': 'ACCEPT', 'T0': fin(0, t3), 'T1': fin(1, t3)})}

    def sb(t0, t3):
        return {'op': 'load', 'dst': 'b', 'addr': 1, 'next': instantiate(
            T2[t0, t3], 'b', f'b{t0}{t3}', {'FAIL': 'ACCEPT', 'T0': sc(0, t3), 'T1': sc(1, t3)})}

    def sa(t3):
        return {'op': 'load', 'dst': 'a', 'addr': 0, 'next': instantiate(
            T1[t3], 'a', f'a{t3}', {'FAIL': 'ACCEPT', 'T0': sb(0, t3), 'T1': sb(1, t3)})}

    program = {'op': 'load', 'dst': 'd', 'addr': 3, 'next':
               {'op': 'br', 'cmp': 'lt', 'a': 'd', 'b': 8, 'then': sa(0), 'else': sa(1)}}
    return worst, program


def build_state():
    V4, T4 = {}, {}
    for t2 in (0, 1):
        for l0 in (0, 1):
            labels = [int(w in SAFE and (t2 or low(w)) and (l0 or top(w))) for w in range(16)]
            V4[t2, l0], T4[t2, l0] = solve_single(labels, [0, 0], ['FAIL', 'OK'], f's4_{t2}{l0}')

    def stage(nextcost, name):
        V, T = {}, {}
        for tprev in (0, 1):
            for l0 in (0, 1):
                labels = [(1 + top(w) if (w in SAFE and (tprev or low(w))) else 0) for w in range(16)]
                costs = [0, nextcost[0, l0], nextcost[1, l0]]
                V[tprev, l0], T[tprev, l0] = solve_single(labels, costs, ['FAIL', 'T0', 'T1'], f'{name}_{tprev}{l0}')
        return V, T

    V3, T3 = stage(V4, 's3')
    V2, T2 = stage(V3, 's2')
    labels = [(1 + 2 * top(w) + low(w) if w in SAFE else 0) for w in range(16)]
    costs = [0] + [V2[t0, l0] for t0 in (0, 1) for l0 in (0, 1)]
    V1, T1 = solve_single(labels, costs, ['FAIL', 'S00', 'S01', 'S10', 'S11'], 's1')
    print('state variant: V4', V4, 'V3', V3, 'V2', V2, 'V1', V1, '-> worst non-load steps', V1)

    def fin(t2, l0):
        return {'op': 'load', 'dst': 'd', 'addr': 3, 'next': instantiate(
            T4[t2, l0], 'd', f'd{t2}{l0}', {'FAIL': 'ACCEPT', 'OK': 'REJECT'})}

    def sc(t1, l0):
        return {'op': 'load', 'dst': 'c', 'addr': 2, 'next': instantiate(
            T3[t1, l0], 'c', f'c{t1}{l0}', {'FAIL': 'ACCEPT', 'T0': fin(0, l0), 'T1': fin(1, l0)})}

    def sb(t0, l0):
        return {'op': 'load', 'dst': 'b', 'addr': 1, 'next': instantiate(
            T2[t0, l0], 'b', f'b{t0}{l0}', {'FAIL': 'ACCEPT', 'T0': sc(0, l0), 'T1': sc(1, l0)})}

    leaves = {'FAIL': 'ACCEPT'}
    for t0 in (0, 1):
        for l0 in (0, 1):
            leaves[f'S{t0}{l0}'] = sb(t0, l0)
    program = {'op': 'load', 'dst': 'a', 'addr': 0, 'next': instantiate(T1, 'a', 'a', leaves)}
    return V1, program


def report(name, program):
    errors, hist, worst = evaluate(program)
    print(f'{name}: errors {len(errors)}, worst case {worst[0]} steps, histogram {hist}')
    print(f'{name}: first worst-case masks', [f'{m:04x}' for m in worst[1]])
    assert not errors
    with open(os.path.join(WORK, f'program_{name}.json'), 'w') as out:
        json.dump(program, out)
    return worst[0]


if __name__ == '__main__':
    wp, prog_p = build_probe()
    tp = report('probe', prog_p)
    ws, prog_s = build_state()
    ts = report('state', prog_s)
    print(f'solver calls: {calls}; probe variant worst {tp} (4 loads + {wp}); state variant worst {ts} (4 loads + {ws})')
