#!/usr/bin/env python3
"""Run the journal's 26-instruction table_index_lookup.asm (the F5' decider) on the proof's F5 files built
by table_index_family_generator.py (canonical order, heap names, rule width), against T(u).  The journal note says failure
there is expected but unchecked.  Run from audits/: python3 table_index_lookup_on_padded_family.py   (nothing is written)"""
import sys, random
sys.dont_write_bytecode = True
import table_index_family_generator as F
import five_slot_ram_interpreter as J
prog = J.parse(open('table_index_lookup.asm').read())
rng = random.Random(11)
tot = ok = 0
for t in (7, 8):
    for k in range(8):
        T = [rng.randrange(2) for _ in range(1 << t)]
        u = [rng.randrange(2) for _ in range(t)]
        T[int(''.join(map(str, u)), 2)] = k % 2
        probe = F.build(t, T, u, z=0)
        z = [0, 1, probe['L'] // 2, probe['L'] - 1][k % 4]
        f = F.build(t, T, u, z=z)
        nwords = (len(f['data']) + f['W'] - 1) // f['W']
        v, steps = J.run(prog, f['data'], w=f['w'], max_steps=60 * nwords)
        truth = F.truth(T, u)
        good = v == ('YES' if truth else 'NO')
        tot += 1; ok += good
        print('t=%d w=%d z=%6d truth=%-5s verdict=%-7s steps=%d %s' % (t, f['w'], z, truth, v, steps, '' if good else 'WRONG'))
print('table_index_lookup.asm on F5: files=%d correct=%d wrong=%d' % (tot, ok, tot - ok))
