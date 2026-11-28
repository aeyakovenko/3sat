#!/usr/bin/env python3
"""The four 87-byte equality files of notes/five-instructions-cannot-decide-dimacs-sat.md (w = 16).
(1) the journal's 5-instruction positive control (2 direct LOADs, 3 branches) decides them;
(2) exhaustive check of the straight-line 4-instruction shape  x=load 34; y=load 39; z=op(.,.); br cmp(.,.)
    over all 12 ops, operand roles, all 2^16 literals and the 4 branch comparisons."""
import sys
sys.dont_write_bytecode = True
from itertools import product
import numpy as np
import five_slot_ram_interpreter as I
import equality_file_generator as G

fixed = [(x, 2 * y, 3 * z) for x, y, z in product((1, -1), repeat=3) if (y, z) != (1, 1)]
prefix = b'p cnf 3 8\n' + b''.join((' '.join(map(str, c)) + ' 0\n').encode() for c in fixed)
files = [prefix + s + b'1 2 3 0\n' + t + b'1 2 3 0\n' for s, t in product((b' ', b'-'), repeat=2)]
truth = [G.cadical_sat(G.validate(dict(data=f))) for f in files]
print('lengths', {len(f) for f in files}, 'CaDiCaL SAT', truth)
w34 = sorted({int.from_bytes(f[68:70], 'little') for f in files}); w39 = sorted({int.from_bytes(f[78:80], 'little') for f in files})
pc = I.parse("""x = load 34
y = load 39
br eq x %d A B
A: br eq y %d YES NO
B: br eq y %d NO YES
""" % (w34[0], w39[0], w39[0]))
p4 = I.parse(open('four_file_four_instructions.asm').read())
print('4-instruction program four_file_four_instructions.asm:', [I.run(p4, f, w=16)[0] for f in files])
print('5-instruction control:', [I.run(pc, f, w=16)[0] for f in files])
words = [(int.from_bytes(f[68:70], 'little'), int.from_bytes(f[78:80], 'little')) for f in files]
X = np.array([a for a, b in words], dtype=np.int64); Y = np.array([b for a, b in words], dtype=np.int64)
T = np.array(truth)
M = 0xFFFF
c = np.arange(65536, dtype=np.int64)
def ops(a, b):
    out = {'add': (a + b) & M, 'sub': (a - b) & M, 'mul': (a * b) & M, 'and': a & b, 'or': a | b, 'xor': a ^ b,
           'shl': np.where(b < 16, (a << np.minimum(b, 15)) & M, 0), 'shr': np.where(b < 16, a >> np.minimum(b, 15), 0),
           'eq': (a == b).astype(np.int64), 'ne': (a != b).astype(np.int64), 'ltu': (a < b).astype(np.int64), 'mov': a}
    return out
def cmp(name, a, b):
    return {'eq': a == b, 'ne': a != b, 'ltu': a < b, 'geu': a >= b}[name]
found = []
# (i) z = op(x,y) or op(y,x); branch z against any literal L or against x / y, either order
for (a, b, tag) in ((X, Y, 'xy'), (Y, X, 'yx')):
    for op, z in ops(a, b).items():
        for cn in ('eq', 'ne', 'ltu', 'geu'):
            for lhs, rhs, t2 in ((z[:, None], c[None, :], 'z?L'), (c[None, :], z[:, None], 'L?z')):
                r = cmp(cn, lhs, rhs)                    # 4 x 65536
                good = np.all(r == T[:, None], axis=0) | np.all(r == ~T[:, None], axis=0)
                if good.any(): found.append((tag, op, cn, t2, int(np.argmax(good))))
            for other, t3 in ((X, 'x'), (Y, 'y')):
                for r in (cmp(cn, z, other), cmp(cn, other, z)):
                    if np.all(r == T) or np.all(r == ~T): found.append((tag, op, cn, t3))
# (ii) z = op(x, L) / op(L, x) (and with y); branch z against the other register
for (a, other, tag) in ((X, Y, 'x'), (Y, X, 'y')):
    for order in (0, 1):
        A = a[:, None]; Cc = c[None, :]
        for op, z in (ops(A, Cc) if order == 0 else ops(Cc, A)).items():
            for cn in ('eq', 'ne', 'ltu', 'geu'):
                for r in (cmp(cn, z, other[:, None]), cmp(cn, other[:, None], z)):
                    good = np.all(r == T[:, None], axis=0) | np.all(r == ~T[:, None], axis=0)
                    if good.any(): found.append((tag, order, op, cn, int(np.argmax(good))))
print('straight-line 4-instruction programs deciding the four files:', len(found), found[:5])
# (iii) 3 stored instructions: two direct LOADs and one branch comparing the two words (any order, any test)
three = [(cn, o) for cn in ('eq', 'ne', 'ltu', 'geu') for o in (0, 1)
         if (lambda r: np.all(r == T) or np.all(r == ~T))(cmp(cn, X, Y) if o == 0 else cmp(cn, Y, X))]
print('3-instruction programs x=load 34; y=load 39; br cmp x y deciding the files:', three, ' words(34,39):', [hex(a) + '/' + hex(b) for a, b in words])
