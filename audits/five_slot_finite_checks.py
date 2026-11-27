#!/usr/bin/env python3
"""Finite checks for the five-slot case split, written from the notes' definitions
(no journal code imported).
1. Four proper 3-CNF files (a layout of their own, not the journal's 87-byte files): six
   common clauses forbid every assignment with (x2,x3) != (0,0); two clauses pin x1
   with signs s1, s2.  Check: equal length, SAT iff s1 == s2 (brute force over 8
   assignments from parsed bytes), w = 16, and the files differ in exactly two
   16-bit little-endian words.
2. The two-query graph lemma: all 5^5 = 3125 graphs (start edge + two query
   vertices with two reply edges each, targets {u, v, YES, NO, LOOP}); list the
   total two-bit functions realised.
3. An interpreter for the separate-operation word RAM; positive control: the
   two-direct-LOAD, three-branch program decides the four files.
4. A finite sweep (checked at finite size only): programs with one cycle
   LOAD x<-M[p]; NUM p<-op(a,b); B1; B2 (exits to YES / NO), opcodes add, sub,
   mul, and, or, xor, shl, shr, literals from a small set, branch tests
   (reg ==/< literal) -- does any decide all four files?
Run: python3 five_slot_finite_checks.py [--full | --quick]
By default the sweep is a smoke test that runs every 101st program (a few
seconds); --full runs all 7,225,344 programs (about 8 minutes); --quick skips it.
"""
import itertools, math

def build(s1, s2):
    lit = lambda sg, v: ('-' if sg else ' ') + str(v)
    common = []
    for a1, a2, a3 in itertools.product((0, 1), repeat=3):
        if (a2, a3) == (0, 0):
            continue
        # clause excluding assignment (a1,a2,a3): literal is negated iff variable true
        common.append((a1, a2, a3))
    assert len(common) == 6
    lines = ['p cnf 3 8']
    for a1, a2, a3 in common:
        lines.append(' '.join([lit(a1, 1), lit(a2, 2), lit(a3, 3), '0']))
    # pins: (s x1 | x2 | x3) with x2=x3=0 forced -> unit literal on x1
    lines.append(' '.join([lit(s1, 1), lit(0, 2), lit(0, 3), '0']))
    lines.append(' '.join([lit(s2, 1), lit(0, 2), lit(0, 3), '0']))
    return ('\n'.join(lines) + '\n').encode()

def parse_sat(b):
    toks = b.decode().split()
    assert toks[:4] == ['p', 'cnf', '3', '8']
    nums = list(map(int, toks[4:]))
    clauses, cur = [], []
    for t in nums:
        if t == 0:
            clauses.append(cur); cur = []
        else:
            cur.append(t)
    assert len(clauses) == 8 and all(len(c) == 3 and len({abs(l) for l in c}) == 3 for c in clauses)
    for a in itertools.product((False, True), repeat=3):
        if all(any((l > 0) == a[abs(l) - 1] for l in c) for c in clauses):
            return True
    return False

def words(b, w):
    W = w // 8
    nwords = -(-len(b) // W)
    pad = b + bytes(nwords * W - len(b))
    return [int.from_bytes(pad[i * W:(i + 1) * W], 'little') for i in range(nwords)]

files = {(s1, s2): build(s1, s2) for s1 in (0, 1) for s2 in (0, 1)}
lens = {k: len(v) for k, v in files.items()}
N = 8 * lens[(0, 0)]
w = 16 * math.ceil(math.log2(N + 2) / 16)
print('1. file length bytes', set(lens.values()), 'N bits', N, 'w', w)
sat = {k: parse_sat(v) for k, v in files.items()}
print('   SAT values', sat, ' equals (s1==s2):', all(sat[k] == (k[0] == k[1]) for k in sat))
mem = {k: words(v, w) for k, v in files.items()}
diff = sorted({i for k in mem for i in range(len(mem[k])) if mem[k][i] != mem[(0, 0)][i]})
print('   differing word addresses', diff, ' words per file', len(mem[(0, 0)]))
assert len(diff) == 2
A1, A2 = diff

# 2. two-query graphs
YES, NO, LOOP = 'YES', 'NO', 'LOOP'
targets = ['u', 'v', YES, NO, LOOP]
funcs = set()
for start, uu0, uu1, vv0, vv1 in itertools.product(targets, repeat=5):
    edge = {('u', 0): uu0, ('u', 1): uu1, ('v', 0): vv0, ('v', 1): vv1}
    tab = []
    for bu, bv in itertools.product((0, 1), repeat=2):
        cur, seen, res = start, set(), None
        while True:
            if cur in (YES, NO):
                res = cur; break
            if cur == LOOP or cur in seen:
                res = LOOP; break
            seen.add(cur)
            cur = edge[(cur, bu if cur == 'u' else bv)]
        tab.append(res)
    if LOOP not in tab:
        funcs.add(tuple(t == YES for t in tab))
allf = set(itertools.product((False, True), repeat=4))
EQ = (True, False, False, True); XOR = (False, True, True, False)
print('2. graphs 3125; total functions realised', len(funcs), 'of 16; missing:',
      sorted(['EQ' if f == EQ else 'XOR' if f == XOR else str(f) for f in allf - funcs]))

# 3. interpreter
MASK = (1 << w) - 1
def run(prog, memory, regs0, maxsteps=4000):
    """prog: list of instructions; ('LOAD', d, a) a = reg name or int;
    ('NUM', d, op, o1, o2); ('BR', cmp, o1, o2, t_true, t_false); ('STORE', a, v);
    successor of non-branch i is given by ('next', j) stored as last field."""
    M = dict(enumerate(memory))
    R = dict(regs0)
    val = lambda o: (R.get(o, 0) if isinstance(o, str) else o & MASK)
    pc = 0
    for _ in range(maxsteps):
        if pc in (YES, NO):
            return pc
        ins = prog[pc]
        k = ins[0]
        if k == 'LOAD':
            R[ins[1]] = M.get(val(ins[2]), 0); pc = ins[3]
        elif k == 'STORE':
            M[val(ins[1])] = val(ins[2]); pc = ins[3]
        elif k == 'NUM':
            a, b = val(ins[3]), val(ins[4]); op = ins[2]
            if op == 'add': r = a + b
            elif op == 'sub': r = a - b
            elif op == 'mul': r = a * b
            elif op == 'and': r = a & b
            elif op == 'or': r = a | b
            elif op == 'xor': r = a ^ b
            elif op == 'shl': r = a << (b % w)
            elif op == 'shr': r = a >> (b % w)
            R[ins[1]] = r & MASK; pc = ins[5]
        elif k == 'BR':
            a, b = val(ins[2]), val(ins[3])
            c = (a == b) if ins[1] == 'eq' else (a < b)
            pc = ins[4] if c else ins[5]
    return LOOP

c1 = mem[(0, 0)][A1]; c2 = mem[(0, 0)][A2]
pos = [('LOAD', 'x', A1, 1), ('LOAD', 'y', A2, 2),
       ('BR', 'eq', 'x', c1, 3, 4),
       ('BR', 'eq', 'y', c2, YES, NO),
       ('BR', 'eq', 'y', c2, NO, YES)]
res = {k: run(pos, mem[k], {}) for k in mem}
print('3. positive control (2 direct LOADs, 3 branches):', res,
      ' correct on all four:', all((res[k] == YES) == sat[k] for k in mem))

# 4. finite sweep of one-LOAD two-register programs on the four files
import sys
if '--quick' in sys.argv:
    print('4. sweep skipped (--quick)'); sys.exit(0)
lits =sorted({0, 1, 2, 3, 4, 5, A1, A2, A2 - A1, c1, c2, mem[(1, 1)][A1], mem[(1, 1)][A2]})
ops = ['add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'shr']
srcs = ['x', 'p'] + lits
tests = [(cmp, r, l) for cmp in ('eq', 'lt') for r in ('x', 'p') for l in lits]
full = '--full' in sys.argv
stride = 1 if full else 101
count = 0; tested = 0; found = []
for op in ops:
    for o1 in srcs:
        for o2 in srcs:
            for t1 in tests:
                for t2 in tests:
                    for e1, e2 in ((YES, NO), (NO, YES)):
                        # cycle: 0 LOAD x<-M[p]; 1 NUM p<-op(o1,o2); 2 B1 (true -> exit e1);
                        # 3 B2 (true -> exit e2, false -> back to 0)
                        count += 1
                        if (count - 1) % stride:
                            continue
                        tested += 1
                        prog = [('LOAD', 'x', 'p', 1), ('NUM', 'p', op, o1, o2, 2),
                                ('BR', t1[0], t1[1], t1[2], e1, 3),
                                ('BR', t2[0], t2[1], t2[2], e2, 0)]
                        ok = True
                        for k in mem:
                            r = run(prog, mem[k], {}, maxsteps=400)
                            if r == LOOP or (r == YES) != sat[k]:
                                ok = False; break
                        if ok:
                            found.append(prog)
if full:
    print('4. swept', count, 'programs of the shape LOAD x<-M[p]; NUM p<-op; B1; B2 with', len(lits), 'literals;',
          'deciding all four files:', len(found))
else:
    print('4. smoke test: ran one in %d of the' % stride, count, 'programs of the shape LOAD x<-M[p]; NUM p<-op; B1; B2 with',
          len(lits), 'literals (%d programs; --full runs all);' % tested, 'deciding all four files:', len(found))
for p in found[:5]:
    print('   FOUND', p)
