#!/usr/bin/env python3
"""Play the focus Challenger sigma of notes/frame-value-on-round-robin-ladders.md against an exhaustive Pebbler,
and compare the Pebbler's optimum P*(sigma) with the recursion g_rec and the exact frame values.

Run from audits/:
  python3 frame_game_round_robin_challenger.py [small|large|branches]
compiles frame_game_round_robin_challenger.cpp into a temporary directory (with $CXX, or c++) and runs it under an
8 GB address-space limit and nice 19:
  small    (default) C = 2, 3, 4 and T = C..12, Pebbler modes 0 (any unpebbled node) and 1 (proper ancestors of
           the challenged node only), memo 2^24;
  large    mode 1, memo 2^26 (about 3 GB): (C, T) = (2, 13..18), (3, 13..15), (5, 5..10), (6, 6..9), (4, 13);
  branches the branch counters at (2, 18) and (3, 15) in mode 1 and (4, 11) in mode 0.
Every answer of sigma asserts p in B, Lemma 5's strong form inside the focus with (A)/(B), I(R') and Fact 1; the
script then checks g_rec(T) <= P*(sigma) on every row and P*(sigma) <= V wherever V is known exactly, and exits 1
on a violation or a failed run. Nothing is written.
"""
import os, re, resource, subprocess, sys, tempfile
sys.dont_write_bytecode = True
import frame_game_round_robin_recursion as rec

HERE = os.path.dirname(os.path.abspath(__file__))
CAP = 8 << 30
RUNS = {
    'small': [(C, T, r, 24) for C in (2, 3, 4) for T in range(C, 13) for r in (0, 1)],
    'large': [(C, T, 1, 26) for C, Ts in ((2, range(13, 19)), (3, range(13, 16)), (5, range(5, 11)), (6, range(6, 10)), (4, [13]))
              for T in Ts],
    'branches': [(2, 18, 1, 26), (3, 15, 1, 26), (4, 11, 0, 24)],
}
PAT = re.compile(r"sigma C=(\d+) T=(\d+) n=(\d+) restrict=(\d): Pstar (>=|>)?\s*(\d+)")


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (CAP, CAP))
    os.nice(19)


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'small'
    out = []
    with tempfile.TemporaryDirectory() as temp:
        exe = os.path.join(temp, 'challenger')
        subprocess.run([os.environ.get('CXX', 'c++'), '-O2', '-std=c++17', '-o', exe,
                        os.path.join(HERE, 'frame_game_round_robin_challenger.cpp')], check=True)
        for C, T, r, lg in RUNS[which]:
            p = subprocess.run([exe, str(C), str(T), str(r), str(lg), '40'], stdout=subprocess.PIPE,
                               stderr=subprocess.DEVNULL, text=True, preexec_fn=limits)
            lines = p.stdout.splitlines() if which == 'branches' else [l for l in p.stdout.splitlines() if l.startswith('sigma')]
            if p.returncode != 0 or not lines:
                lines = [f'C={C} T={T} R={r} exit {p.returncode}']
            out += lines
    if which == 'branches':
        print('\n'.join(out))
        return
    rows = {}
    bad = 0
    asserts = sum(int(m.group(1)) for m in (re.search(r'asserts (\d+)', l) for l in out) if m)
    for line in out:
        m = PAT.search(line)
        if not m:
            print('FAILED RUN', line)
            bad += 1
            continue
        C, T, n, r = (int(m.group(i)) for i in (1, 2, 3, 4))
        rows[(C, T, r)] = (int(m.group(6)), m.group(5), n)
    print('C T n | g_rec | Pstar(any move) | Pstar(ancestors of uc) | exact V | f_C')
    gtab = {}
    for (C, T) in sorted({(c, t) for (c, t, r) in rows}):
        if C not in gtab:
            gtab[C] = rec.grec(C, 60)
        g = gtab[C][T]
        V = rec.EXACT.get((C, T))
        cells = []
        for r in (0, 1):
            if (C, T, r) not in rows:
                cells.append('-')
                continue
            k, rel, n = rows[(C, T, r)]
            cells.append(f"{'>=' if rel else ''}{k}")
            if not rel and g > k:
                bad += 1
                print('VIOLATION g_rec > Pstar', C, T, r)
            if not rel and V is not None and k > V:
                bad += 1
                print('VIOLATION Pstar > exact V', C, T, r)
        Vs = str(V) if V is not None else (f'>={rec.LOWER[(C, T)]}' if (C, T) in rec.LOWER else '?')
        n = [v[2] for key, v in rows.items() if key[:2] == (C, T)][0]
        print(f'{C} {T} {n} | {g} | {cells[0]} | {cells[1]} | {Vs} | {rec.fC(C, T)}')
    print(f'runs {len(out)}, rule-1 answers with Lemma 5 asserted: {asserts}')
    print(f'violations {bad}')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
