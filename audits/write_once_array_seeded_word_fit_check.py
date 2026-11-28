"""Word-fit check, written during review, for the seeded packed-presence-table array (Z1+) of
notes/ram-time-t-in-word-priced-alternating-time-t-over-log-log-t.md: every cell the scheme writes must fit
in one w-bit word, and presence words must fit in B^2 bits. It wraps the memory of
write_once_array_seeded_independent_simulator.py and records the largest bit length written per kind of cell.

Run from audits/: python3 write_once_array_seeded_word_fit_check.py   (twelve runs, about a minute; nothing is
written). An assertion fails if a value does not fit.
"""
import random, sys
sys.dont_write_bytecode = True
import write_once_array_seeded_independent_simulator as Z
def run(w, beta, n, fams, seeds):
    B = 1 << beta
    for fam in fams:
        ops = Z.sequence(fam, n, w, random.Random(5))
        for s in range(seeds):
            S = Z.Z1plus(w, beta, Z.good_seed(w, random.Random(77 + s)))
            mx = {'entries': 0, 'directory': 0, 'presence': 0}
            orig = S.m.write
            def wr(a, v, S=S, mx=mx, orig=orig):
                assert 0 <= v < (1 << w), ("value does not fit in a word", a, v)
                if a < (1 << (w - 1)):
                    kind = ['entries', 'directory', 'presence'][(a >> S.RS) % 3]
                    mx[kind] = max(mx[kind], v.bit_length())
                orig(a, v)
            S.m.write = wr
            for op in ops:
                if op[0] == 'u': S.update(op[1], op[2])
                else: S.read(op[1])
            assert mx['presence'] <= B * B
            print("w=%d B=%d n=%d fam=%-6s seed=%d  max bits written: entries %d, directory %d, presence %d (B^2=%d, w=%d)"
                  % (w, B, n, fam, s, mx['entries'], mx['directory'], mx['presence'], B * B, w), flush=True)
for (w, beta, n) in [(32, 2, 4096), (64, 3, 8192), (256, 4, 4096)]:
    run(w, beta, n, ['uni', 'rep', 'cons', 'hot'], 1)
