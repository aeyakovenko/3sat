#!/usr/bin/env python3
"""Run a program on the four 87-byte files (F3) at w = 16 against CaDiCaL.  Run from audits/: python3 four_file_test_any_program.py [PROG.asm]   (default four_file_four_instructions.asm)"""
import sys
sys.dont_write_bytecode = True
from itertools import product
import five_slot_ram_interpreter as I, five_slot_independent_interpreter as R, equality_file_generator as G
fixed = [(x, 2 * y, 3 * z) for x, y, z in product((1, -1), repeat=3) if (y, z) != (1, 1)]
prefix = b'p cnf 3 8\n' + b''.join((' '.join(map(str, c)) + ' 0\n').encode() for c in fixed)
files = [prefix + s + b'1 2 3 0\n' + t + b'1 2 3 0\n' for s, t in product((b' ', b'-'), repeat=2)]
truth = [G.cadical_sat(G.validate(dict(data=f))) for f in files]
text = open(sys.argv[1] if len(sys.argv) > 1 else 'four_file_four_instructions.asm').read()
out = [I.run(I.parse(text), f, w=16) for f in files]
out2 = [R.execute(R.assemble(text), 16, R.file_base(f, 16), 10**6)[:2] for f in files]
assert out == [tuple(o) for o in out2]
print('F3 four files: truth', truth, 'verdicts', [v for v, s in out], 'steps', [s for v, s in out],
      'correct', sum((v == 'YES') == t for (v, s), t in zip(out, truth)), 'of 4')
