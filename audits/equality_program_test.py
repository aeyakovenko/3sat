#!/usr/bin/env python3
"""Run a program on the constant-palette equality files (the journal generator equality_file_generator.py) and
compare with CaDiCaL on the parsed clauses.  Usage: python3 -B equality_program_test.py [PROG.asm [SEED] [COUNT]]
(no arguments: equality_two_cursor_17.asm with seed 7 and 64 files, about 1 s)"""
import sys, random, math
sys.dont_write_bytecode = True
import five_slot_ram_interpreter as I
import equality_file_generator as G

def main():
    prog_path = sys.argv[1] if len(sys.argv) > 1 else 'equality_two_cursor_17.asm'
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else (1 if len(sys.argv) > 1 else 7)
    count = int(sys.argv[3]) if len(sys.argv) > 3 else (40 if len(sys.argv) > 1 else 64)
    prog = I.parse(open(prog_path).read())
    rng = random.Random(seed)
    stats = []
    ok = bad = 0
    # (N, D, CD, forced w): natural widths at 2^14..2^18 bits, plus forced w=48/64
    sizes = [(2**14, 1, 4, 32), (2**15, 1, 6, 32), (2**16, 1, 8, None), (2**17, 1, 12, None),
             (2**18, 1, 16, None), (2**19, 1, 24, None), (2**16, 1, 16, 48), (2**17, 1, 24, 64)]
    for t in range(count):
        N, Dd, CD, wf = sizes[t % len(sizes)]
        f0 = None
        while f0 is None or f0['k'] < 2:
            f0 = G.build(N, Dd, CD, w=wf, rng=rng)
            if f0 is None:
                CD += 1
        k = f0['k']
        a = [rng.randrange(2) for _ in range(k)]
        mode = t % 3
        if mode == 0:
            b = list(a)
        elif mode == 1:
            b = list(a); b[rng.randrange(k)] ^= 1
        else:
            b = [rng.randrange(2) for _ in range(k)]
        f = G.build(N, Dd, CD, w=wf, a_bits=a, b_bits=b, rng=rng)
        cl = G.validate(f)
        truth = G.cadical_sat(cl)
        assert truth == (a == b)
        verdict, steps = I.run(prog, f['data'], w=f['w'], max_steps=50 * N)
        good = (verdict == ('YES' if truth else 'NO'))
        ok += good; bad += (not good)
        stats.append((N, f['w'], k, truth, verdict, steps, steps / N))
        if not good:
            print('MISMATCH', N, f['w'], k, truth, verdict, steps)
    print('prog=%s files=%d correct=%d wrong=%d' % (prog_path, ok + bad, ok, bad))
    print('max steps/N = %.4f   (N in bits)' % max(s[6] for s in stats))
    for N in sorted({s[0] for s in stats}):
        r = [s for s in stats if s[0] == N]
        print('  N=%7d w=%s k=%s  max steps %d  steps/N %.4f' % (N, sorted({s[1] for s in r}), sorted({s[2] for s in r}),
              max(s[5] for s in r), max(s[6] for s in r)))

if __name__ == '__main__':
    main()
