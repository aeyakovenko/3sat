#!/usr/bin/env python3
"""The 50-instruction decider files each pin sign under the lead word of the pin's third literal and walks with the
same base, so it needs that word to be the same in every pin (the theorem's pins are all (+-x a b)). This check
builds 12 files at t = 5 and runs table_index_tree_walk.asm on them unchanged, with every selector pin written
(+-x b a), and with only the pin of the leaf that u selects written (+-x b a); swapping two literals inside a clause
does not change the formula. With that leaf pin swapped, the root's walk reads the leaf's sign under the other base,
finds an empty cell and answers NO, which is wrong exactly when T(u) = 1.
Run from audits/: python3 table_index_tree_walk_third_literal_check.py   (about a second; nothing is written)."""
import sys, random
sys.dont_write_bytecode = True
import table_index_family_generator as F
import five_slot_ram_interpreter as J
prog = J.parse(open('table_index_tree_walk.asm').read())
rng = random.Random(7)
res = {'unchanged': [0, 0, 0], 'selector pins (x, b, a)': [0, 0, 0], 'selected leaf pin (x, b, a)': [0, 0, 0]}
nsat = 0
for k in range(12):
    t = 5
    u = [rng.randrange(2) for _ in range(t)]
    T = [rng.randrange(2) for _ in range(1 << t)]
    f = F.build(t, T, u, z=0, rng=random.Random(k))
    W = f['W']; data = f['data']; truth = F.truth(T, u); nsat += truth
    a = (' ' * (W - 2) + ' 1').encode(); b = (' ' * (W - 2) + ' 2').encode()
    for kind in res:
        d = bytearray(data)
        if kind == 'selector pins (x, b, a)':
            for wi in f['sel_words']:
                p = (wi + 1 + f['K']) * W          # pinned literal: lead word + K digit blocks, then a, b
                assert d[p:p + W] == a and d[p + W:p + 2 * W] == b
                d[p:p + W], d[p + W:p + 2 * W] = b, a
        elif kind == 'selected leaf pin (x, b, a)':
            leaf = (1 << t) + int(''.join(map(str, u)), 2)      # the leaf pinned to T(u)
            name = ('1' + ''.join('0' * (W - 1) + bit for bit in format(f['index'][('n', leaf)], '0%db' % f['K']))).encode()
            for sign in (b' ', b'-'):
                lead = (' ' * (W - 2)).encode() + sign + name
                q = bytes(d).find(lead + a + b)
                if q >= 0 and q % W == 0:
                    p = q + len(lead); d[p:p + W], d[p + W:p + 2 * W] = b, a; break
            else:
                raise AssertionError('leaf pin not found')
        v, steps = J.run(prog, bytes(d), w=f['w'], max_steps=40 * len(d) // W + 10 ** 5)
        good = v == ('YES' if truth else 'NO')
        res[kind][0] += 1; res[kind][1] += good; res[kind][2] += truth and not good
for kind, (n, ok, ws) in res.items():
    print('%-28s files=%d correct=%d wrong=%d, %d of them satisfiable' % (kind, n, ok, n - ok, ws))
print('satisfiable files: %d of %d' % (nsat, res['unchanged'][0]))
