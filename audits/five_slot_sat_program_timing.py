"""Step counts of a RAM program on two explicit families.
U_v: v-variable UNSAT file: clauses (-a -b -c) over consecutive triples covering 1..v
     (all satisfied by all-false), then the 8 sign patterns on 1,2,3.
S_m: SAT file with m clauses (-(3k+1) -(3k+2) -(3k+3)), all names distinct (one attempt).
usage: python3 five_slot_sat_program_timing.py [PROG.asm]   (default five_slot_sat_program_43.asm)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import five_slot_ram_interpreter as ram


def U(v):
    cl = []
    for a in range(1, v + 1):
        b, c = a % v + 1, (a + 1) % v + 1
        cl.append([-a, -b, -c])
    for m in range(8):
        cl.append([(1 if m & 1 else -1) * 1, (1 if m & 2 else -1) * 2, (1 if m & 4 else -1) * 3])
    return 'p cnf %d %d\n' % (v, len(cl)) + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cl)


def S(m):
    cl = [[-(3 * k + 1), -(3 * k + 2), -(3 * k + 3)] for k in range(m)]
    return 'p cnf %d %d\n' % (3 * m, m) + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cl)


path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'five_slot_sat_program_43.asm')
prog = ram.parse(open(path).read())
print('family v bytes steps verdict')
for v in range(3, 10):
    d = U(v).encode()
    r, st = ram.run(prog, d, max_steps=10**10)
    print('U', v, len(d), st, r)
for m in (4, 8, 16, 32, 64):
    d = S(m).encode()
    r, st = ram.run(prog, d, max_steps=10**10)
    print('S', m, len(d), st, r)
