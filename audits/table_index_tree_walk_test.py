#!/usr/bin/env python3
"""Run a program on the proof's F5 files (table_index_family_generator.py) against T(u) and CaDiCaL; both interpreters.
Run from audits/: python3 table_index_tree_walk_test.py [PROG.asm T_LIST FILES_PER_CONFIG [indep=1] [cadical_per_t=4] [C=96] [LIT_ORDER]]
With no argument it runs table_index_tree_walk.asm 5,6 12 1 4 (a few seconds). Nothing is written except CaDiCaL's
temporary files.
Configurations per t: orders {canonical, shuffled, scattered}, naming {heap, random}, z in {0, 1, rand, L-1},
tables {random, indicator of u, complement of indicator}, extra bytes {0..W-1}, final newline or not,
w {rule, forced 48, forced 64}."""
import sys, random, time
sys.dont_write_bytecode = True
import table_index_family_generator as F
import five_slot_ram_interpreter as J
import five_slot_independent_interpreter as R
import equality_file_generator as G

if len(sys.argv) == 1:
    sys.argv += ['table_index_tree_walk.asm', '5,6', '12', '1', '4']
prog_path = sys.argv[1]
ts = [int(x) for x in sys.argv[2].split(',')]
per = int(sys.argv[3])
indep = int(sys.argv[4]) if len(sys.argv) > 4 else 1
ncad = int(sys.argv[5]) if len(sys.argv) > 5 else 4
C = int(sys.argv[6]) if len(sys.argv) > 6 else 96
LIT = sys.argv[7] if len(sys.argv) > 7 else 'theorem'   # literal order inside tree clauses
text = open(prog_path).read()
jp = J.parse(text); rp = R.assemble(text)
print('program %s: %d stored instructions; tree-clause literal order: %s' % (prog_path, len(jp), LIT))
rng = random.Random(2026)
tot = ok = 0
for t in ts:
    worst = {}
    cads = 0
    t0 = time.time()
    for k in range(per):
        order = ['canonical', 'shuffled', 'scattered'][k % 3]
        naming = ['heap', 'random'][(k // 3) % 2]
        wf = [None, None, 48, None, 64, None][k % 6]
        u = [rng.randrange(2) for _ in range(t)]
        tk = k % 4
        if tk == 0:
            T = [rng.randrange(2) for _ in range(1 << t)]
        elif tk == 1:
            ui = int(''.join(map(str, u)), 2); T = [int(i == ui) for i in range(1 << t)]
        elif tk == 2:
            ui = int(''.join(map(str, u)), 2); T = [int(i != ui) for i in range(1 << t)]
        else:
            T = [rng.randrange(2) for _ in range(1 << t)]
            T[int(''.join(map(str, u)), 2)] = k % 2
        Ck = C
        while True:   # forced wider words need a larger length constant for the formula to fit
            probe = F.build(t, T, u, z=0, C=Ck, w=wf, order=order, naming=naming, rng=random.Random(k), lit_order=LIT)
            if probe is not None: break
            Ck *= 2
        L = probe['L']
        z = [0, 1, rng.randrange(L), L - 1][(k // 2) % 4]
        extra = rng.randrange(probe['W'])
        newline = (k % 5 == 0)
        f = F.build(t, T, u, z=z, C=Ck, w=wf, order=order, naming=naming, rng=random.Random(k),
                    extra=extra, newline=newline, lit_order=LIT)
        truth = F.truth(T, u)
        if cads < ncad:
            s = G.cadical_sat(G.validate(dict(data=f['data'])))
            assert s == truth, 'cadical disagrees with T(u)'
            cads += 1
        nwords = (len(f['data']) + f['W'] - 1) // f['W']
        cap = 40 * nwords + 10 ** 5
        v, steps = J.run(jp, f['data'], w=f['w'], max_steps=cap)
        if indep:
            v2, s2, _ = R.execute(rp, f['w'], R.file_base(f['data'], f['w']), cap)
            assert (v2, s2) == (v, steps) or (v2 == 'CAP' and v == 'TIMEOUT'), ((v, steps), (v2, s2))
        good = v == ('YES' if truth else 'NO')
        tot += 1; ok += good
        key = 'rule' if wf is None else 'forced%d' % wf
        spw = steps * f['w'] / f['n']
        worst[key] = max(worst.get(key, 0), spw)
        if not good:
            print('WRONG t=%d order=%s naming=%s w=%s z=%d/%d extra=%d nl=%s truth=%s verdict=%s steps=%d'
                  % (t, order, naming, f['w'], z, L, extra, newline, truth, v, steps))
    print('t=%d files=%d cadical=%d  max steps per file word: %s  (%.0fs)'
          % (t, per, cads, ', '.join('%s %.2f' % kv for kv in sorted(worst.items())), time.time() - t0))
print('files=%d correct=%d wrong=%d' % (tot, ok, tot - ok))
