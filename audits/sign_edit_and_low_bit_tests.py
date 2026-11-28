#!/usr/bin/env python3
"""Test the F1 (periodic sign-edit) and F2 (two-zero-low-bit) deciders on actual files against CaDiCaL."""
import sys, random
sys.dont_write_bytecode = True
from itertools import product
import five_slot_ram_interpreter as I
import equality_file_generator as G
import dimacs_five_slot_layout as L
import read_only_two_alu_audit as R

def f1_files(j, w, rng, edits):
    total = 10 ** j
    header = f'p cnf 20 {total}'.encode('ascii')
    header += (b' ' if len(header) % 2 == 0 else b'') + b'\n'
    pins = [L.record((var, 8, 20), (False, a, b)) for var in (2, 4, 6) for a, b in product((False, True), repeat=2)]
    base = L.record((2, 4, 6), (False, False, False))
    alt = L.record((2, 4, 6), (True, True, True))
    prefix = header + b''.join(pins)
    data = bytearray(prefix + base * (total - len(pins)))
    W = w // 8
    first = (len(prefix) + W - 1) // W
    stop = len(data) // W                    # words [first, stop) are full tail words
    cand = []
    for a in range(first + 8, stop):         # sensitive words used: full tail words from first+8 on
        start = (len(prefix) - a * W) % len(base)
        if start + len(base) <= W:
            cand.append((a, start))
    out = [('base', bytes(data))]
    for a, start in rng.sample(cand, min(edits, len(cand))) + [cand[0], cand[-1]]:
        e = bytearray(data)
        e[a * W + start: a * W + start + len(base)] = alt
        out.append(('edit@%d' % a, bytes(e)))
    return out, len(base), len(cand)

def f2_files(j, rng, edits):
    data, W, hlen, count = R.aligned_base(j)
    data = bytearray(data)
    # clause c (0-based) starts at hlen + 5*W*c; the 7 forcing clauses come first
    out = [('base', bytes(data))]
    for c in rng.sample(range(7, count), edits) + [7, count - 1]:
        e = bytearray(data)
        pos = hlen + 5 * W * c + 1
        assert e[pos] == ord(' ') and e[pos + 1] == ord('1')
        e[pos] = ord('-')
        out.append(('edit@clause%d' % c, bytes(e)))
    return out, W

def check(prog_path, files, w):
    prog = I.parse(open(prog_path).read())
    ok = bad = 0; worst = 0
    for tag, data in files:
        cl = G.validate(dict(data=data))
        truth = G.cadical_sat(cl)
        verdict, steps = I.run(prog, data, w=w, max_steps=40 * 8 * len(data))
        good = verdict == ('YES' if truth else 'NO')
        ok += good; bad += not good
        worst = max(worst, steps / (8 * len(data)))
        if not good:
            print('  MISMATCH', tag, truth, verdict, steps)
    return ok, bad, worst

if __name__ == '__main__':
    rng = random.Random(5)
    for j, w in ((3, 224), (3, 256), (4, 224), (4, 512)):
        files, blen, ncand = f1_files(j, w, rng, 12)
        ok, bad, worst = check('sign_edit_periodic_scan.asm', files, w)
        print('F1 j=%d forced w=%d record=%dB sensitive words used=%d files=%d correct=%d wrong=%d max steps/N=%.4f'
              % (j, w, blen, ncand, ok + bad, ok, bad, worst))
    for j in (2, 3):
        files, W = f2_files(j, rng, 12)
        w = 8 * W
        ok, bad, worst = check('two_low_bit_count.asm', files, w)
        print('F2 j=%d w=%d files=%d correct=%d wrong=%d max steps/N=%.4f' % (j, w, ok + bad, ok, bad, worst))
