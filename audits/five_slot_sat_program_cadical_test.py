"""Test a RAM program (assembly file) against CaDiCaL on random proper DIMACS 3-CNF files, for
a-43-instruction-sat-program-in-the-five-slot-machine.md.
usage: python3 five_slot_sat_program_cadical_test.py PROG.asm SEED COUNT [mode]
       (no arguments: a 20-file smoke test of five_slot_sat_program_43.asm, seed 11, mode small)
modes: small (w=16 by rule), w32 (files padded past 8192 bytes, w=32 by rule),
       forced48 / forced64 (same small files, width forced off-rule to test width-independence)
CaDiCaL is found via $CADICAL, PATH or a Lean toolchain; each formula is piped on stdin.
"""
import random, subprocess, sys, os, time
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import five_slot_ram_interpreter as ram

def find_cadical():
    from shutil import which
    found = os.environ.get("CADICAL") or which("cadical")
    if found:
        return found
    candidates = sorted((Path.home() / ".elan/toolchains").glob("*/bin/cadical"))
    if candidates:
        return str(candidates[0])
    raise SystemExit("cadical not found: set CADICAL, put it on PATH or install a Lean toolchain")


CADICAL = find_cadical()
WS = [' ', '\t', '\n', '\r', '\v', '\f']


def ws(rng, lo=1, hi=3):
    k = rng.randint(lo, hi)
    return ''.join(rng.choice(WS) if rng.random() < 0.4 else ' ' for _ in range(k))


def names_for(rng, nv):
    style = rng.choice(['dense', 'sparse', 'long', 'suffix', 'mixed'])
    if style == 'dense':
        return [str(k + 1) for k in range(nv)], style
    pool = set()
    while len(pool) < nv:
        if style == 'sparse':
            s = str(rng.randint(1, 10**6))
        elif style == 'long':
            s = str(rng.randint(1, 9)) + ''.join(rng.choice('0123456789') for _ in range(rng.randint(15, 45)))
        elif style == 'suffix':  # names that are suffixes / prefixes of one another
            base = rng.choice(['12', '123', '1123', '23', '3', '2', '312', '1212', '21', '1'])
            s = base if rng.random() < 0.5 else str(rng.randint(1, 9)) + base
        else:
            s = rng.choice([str(rng.randint(1, 30)),
                            str(rng.randint(1, 9)) + ''.join(rng.choice('0123456789') for _ in range(rng.randint(5, 25)))])
        pool.add(s)
    return sorted(pool, key=lambda t: (len(t), t)), style


def make_formula(rng):
    nv = rng.randint(3, 6)
    kind = rng.random()
    if kind < 0.3:
        nc = 8
        vs = rng.sample(range(nv), 3)
        clauses = [[(vs[0], (m >> 0) & 1), (vs[1], (m >> 1) & 1), (vs[2], (m >> 2) & 1)] for m in range(8)]
        if rng.random() < 0.5:  # drop one pattern -> SAT
            clauses.pop(rng.randrange(8))
    else:
        nc = rng.randint(1, int(9 * nv))
        clauses = []
        for _ in range(nc):
            vs = rng.sample(range(nv), 3)
            clauses.append([(v, rng.randint(0, 1)) for v in vs])
    rng.shuffle(clauses)
    return nv, clauses


def render(rng, nv, clauses, names, style):
    maxname = max(int(s) for s in names)
    if rng.random() < 0.5:
        V = maxname
    else:
        V = maxname + rng.randint(0, 10**rng.randint(1, 30))
    out = []
    if rng.random() < 0.3:
        out.append(ws(rng))
    out.append('p' + ws(rng) + 'cnf' + ws(rng) + str(V) + ws(rng) + str(len(clauses)))
    for cl in clauses:
        toks = [('-' if neg else '') + names[v] for v, neg in cl] + ['0']
        out.append(ws(rng, 1, 3))
        out.append(ws(rng, 1, 2).join(toks))
    r = rng.random()
    if r < 0.5:
        out.append('\n')
    elif r < 0.8:
        out.append(ws(rng))
    return ''.join(out)


def cadical(nv, clauses):
    used = sorted({v for cl in clauses for v, _ in cl})
    ren = {v: k + 1 for k, v in enumerate(used)}
    txt = 'p cnf %d %d\n' % (len(used), len(clauses)) + ''.join(
        ' '.join(str(-ren[v] if neg else ren[v]) for v, neg in cl) + ' 0\n' for cl in clauses)
    r = subprocess.run([CADICAL, '-q'], input=txt.encode('ascii'), capture_output=True)
    return {10: 'YES', 20: 'NO'}[r.returncode]


def main():
    args = sys.argv[1:] or [os.path.join(os.path.dirname(os.path.abspath(__file__)), 'five_slot_sat_program_43.asm'), '11', '20']
    prog = ram.parse(open(args[0]).read())
    seed, count = int(args[1]), int(args[2])
    mode = args[3] if len(args) > 3 else 'small'
    rng = random.Random(seed)
    stats = {'YES': 0, 'NO': 0}
    widths = set()
    maxsteps = 0
    t0 = time.time()
    for t in range(count):
        nv, clauses = make_formula(rng)
        names, style = names_for(rng, nv)
        txt = render(rng, nv, clauses, names, style)
        if mode == 'w32':
            txt += ' ' * max(0, 8200 - len(txt))
        data = txt.encode('ascii')
        w = {'forced48': 48, 'forced64': 64}.get(mode)
        if w is None:
            w = ram.width_for(len(data))
        widths.add(w)
        truth = cadical(nv, clauses)
        got, steps = ram.run(prog, data, w=w, max_steps=3 * 10**8)
        maxsteps = max(maxsteps, steps)
        if got != truth:
            print('MISMATCH seed=%d test=%d style=%s truth=%s got=%s steps=%d' % (seed, t, style, truth, got, steps))
            print(repr(txt[:400]))
            sys.exit(1)
        stats[truth] += 1
    print('ok prog=%s mode=%s seed=%d tests=%d SAT=%d UNSAT=%d widths=%s max_steps=%d time=%.0fs stored_instructions=%d' % (
        os.path.basename(args[0]), mode, seed, count, stats['YES'], stats['NO'], sorted(widths), maxsteps,
        time.time() - t0, len(prog)))


if __name__ == '__main__':
    main()
