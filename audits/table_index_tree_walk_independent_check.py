#!/usr/bin/env python3
"""Independent check, written during review: run a program with the independent interpreter on the independent
generator's files (table_index_family_generator_independent.py) against T(u); CaDiCaL on a subset; byte-compare them
with table_index_family_generator.py's files where the choices agree.
Run from audits/: python3 table_index_tree_walk_independent_check.py [PROG T_LIST NFILES NCAD LIT_ORDER [variant]]
With no argument it runs table_index_tree_walk.asm 5,6,7 16 16 theorem (a few seconds). Variants: plain, short789,
gadget_zba, C40, C400. Nothing is written except CaDiCaL's temporary files."""
import sys, random, time
sys.dont_write_bytecode = True
import five_slot_block_interpreter_independent as RI, table_index_family_generator_independent as RG, table_index_family_generator as F, equality_file_generator as G
if len(sys.argv) == 1:
    sys.argv += ['table_index_tree_walk.asm', '5,6,7', '16', '16', 'theorem']
prog, issues = RI.parse(open(sys.argv[1]).read()); assert not issues, issues
fn, _ = RI.compile_prog(prog)
ts = [int(x) for x in sys.argv[2].split(',')]
nf = int(sys.argv[3]); ncad = int(sys.argv[4]); LIT = sys.argv[5]
variant = sys.argv[6] if len(sys.argv) > 6 else 'plain'
rng = random.Random(77)
tot = ok = same = cmpd = 0
for t in ts:
    worst = 0.0; cads = 0; t0 = time.time(); verdicts = {}
    for k in range(nf):
        u = [rng.randrange(2) for _ in range(t)]
        T = [rng.randrange(2) for _ in range(1 << t)]
        T[int(''.join(map(str, u)), 2)] = k % 2          # half the files SAT, half UNSAT
        order = ['canonical', 'shuffled'][k % 2]
        naming = ['heap', 'random'][(k // 2) % 2]
        extra = rng.randrange(4); nl = (k % 3 == 0)
        kw = dict(order=order, naming=naming, seed=k, lit_order=LIT, extra=extra, final_newline=nl)
        if variant == 'short789':
            kw['short'] = ('7', '8', '9')
        if variant == 'gadget_zba':
            kw['gadget_order'] = ('z', 'b', 'a')
        Cc = 96
        if variant == 'C40':
            Cc = 40
        if variant == 'C400':
            Cc = 400
        nbytes = -(-Cc * 2 * (2 ** t) * t * t // 8) + extra
        W = RG.width(8 * nbytes) // 8
        probe = RG.build(t, T, u, 0, W, C=Cc, **kw)
        L = probe['L']
        z = [0, 1, rng.randrange(L), L - 1][k % 4]
        f = RG.build(t, T, u, z, W, C=Cc, **kw)
        if order == 'canonical' and naming == 'heap' and variant == 'plain':
            g = F.build(t, T, u, z=z, C=Cc, order='canonical', naming='heap', extra=extra, newline=nl, lit_order=LIT)
            cmpd += 1; same += (g['data'] == f['data'] and g['w'] == f['w'])
        truth = RG.truth(T, u)
        if cads < ncad:
            cl = RG.dimacs_clauses(f['data'])
            assert G.cadical_sat(cl) == truth, 'cadical'
            cads += 1
        nwords = -(-len(f['data']) // W)
        v, steps, sd = RI.run_file(fn, f['data'], f['w'], 60 * nwords + 10 ** 5)
        good = v == ('YES' if truth else 'NO')
        verdicts[v] = verdicts.get(v, 0) + 1
        tot += 1; ok += good
        worst = max(worst, steps * f['w'] / f['n'])
        if sd: print('  shift-convention disagreement count', sd)
        if not good:
            print('  WRONG t=%d k=%d order=%s naming=%s z=%d/%d truth=%s verdict=%s steps=%d' % (t, k, order, naming, z, L, truth, v, steps))
    print('t=%d w=%d files=%d cadical=%d verdicts=%s max steps/word %.2f (%.0fs)' % (t, f['w'], nf, cads, verdicts, worst, time.time() - t0), flush=True)
print('%s lit=%s variant=%s: files=%d correct=%d wrong=%d; generator byte-identical %d/%d' % (sys.argv[1], LIT, variant, tot, ok, tot - ok, same, cmpd))
