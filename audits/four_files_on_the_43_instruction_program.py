#!/usr/bin/env python3
"""The journal's 43-instruction program on the four 87-byte equality files (any-speed check)."""
import sys
sys.dont_write_bytecode = True
from itertools import product
import five_slot_ram_interpreter as I
fixed = [(x, 2 * y, 3 * z) for x, y, z in product((1, -1), repeat=3) if (y, z) != (1, 1)]
prefix = b'p cnf 3 8\n' + b''.join((' '.join(map(str, c)) + ' 0\n').encode() for c in fixed)
files = [prefix + s + b'1 2 3 0\n' + t + b'1 2 3 0\n' for s, t in product((b' ', b'-'), repeat=2)]
p = I.parse(open('five_slot_sat_program_43.asm').read())
print('43-instruction program on the four files:', [I.run(p, f) for f in files])
