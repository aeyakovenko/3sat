#!/usr/bin/env python3
"""Every selector string u, for three tables (random, its complement, parity of u), at t = 5 and 6, canonical
and shuffled order, heap and random names, z = 0 and L-1: PROG against T(u); both interpreters.
Run from audits/: python3 table_index_tree_walk_every_u.py [PROG.asm]   (default table_index_tree_walk.asm; nothing is written)"""
import sys, random
sys.dont_write_bytecode = True
import table_index_family_generator as F, five_slot_ram_interpreter as J, five_slot_independent_interpreter as R
if len(sys.argv) == 1:
    sys.argv.append('table_index_tree_walk.asm')
text = open(sys.argv[1]).read(); jp = J.parse(text); rp = R.assemble(text)
rng = random.Random(3); tot = ok = 0
for t in (5, 6):
    Tr = [rng.randrange(2) for _ in range(1 << t)]
    for T in (Tr, [1 - b for b in Tr], [bin(i).count('1') % 2 for i in range(1 << t)]):
        for k, (order, naming) in enumerate((('canonical', 'heap'), ('shuffled', 'random'))):
            for ui in range(1 << t):
                u = [int(c) for c in format(ui, '0%db' % t)]
                L = F.build(t, T, u, order=order, naming=naming, rng=random.Random(k))['L']
                f = F.build(t, T, u, z=(0 if ui % 2 else L - 1), order=order, naming=naming, rng=random.Random(k))
                v, s = J.run(jp, f['data'], w=f['w'], max_steps=10 ** 7)
                v2, s2, _ = R.execute(rp, f['w'], R.file_base(f['data'], f['w']), 10 ** 7)
                assert (v, s) == (v2, s2)
                tot += 1; ok += v == ('YES' if F.truth(T, u) else 'NO')
print('%s: every u at t = 5, 6, three tables, two order/naming settings: files=%d correct=%d wrong=%d' % (sys.argv[1], tot, ok, tot - ok))
