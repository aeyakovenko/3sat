"""what transfers to SAT encodings.

  F  the journal's two-record DIMACS families: the scan programs use only
     add / load / eq-branch (executed here with every other operation
     disabled); fooling families there have at most m members; count of
     well-formed lattice points on one concrete segment (16-byte words)
  G  a binary one-literal-per-word 3-CNF encoding with the sign in the low
     bit: brute-force check of the fooling property on tiny parameters, the
     threshold T0 of Theorem 1 for it, and a scan-time 20-operation solver

Usage: python3 -B knapsack_sat_transfer_audit.py
"""
import random
import sys
from itertools import product
from math import gcd

sys.dont_write_bytecode = True
from integer_ram_step_model import ADDITIVE, RAM
from knapsack_fooling_family_audit import A_bound, H_int, T0

ADD_OK = ADDITIVE | {'load', 'store'}
SCAN_OK = {'add', 'load', 'eq'}                    # everything else is disabled in section F


# ----------------------------------------------------------------- F
def section_F():
    print('== F. Two-record DIMACS families (words A / B as in two-instructions-per-homogeneous-dimacs-word.md)')
    width = 16                                            # bytes per word, w = 128
    a, b = '10000019', '10000033'                         # names forced true / false by the public prefix
    word = lambda name: int.from_bytes((name + ' 1 2 0\n').ljust(width).encode(), 'little')
    A, B = word(a), word(b)
    m = 1000
    rng = random.Random(14)
    for label, flips in (('all A (satisfiable)', []), ('one B (unsatisfiable)', [rng.randrange(m)])):
        x = [B if i in flips else A for i in range(m)]
        ram = RAM(x, w=8 * width, allowed=SCAN_OK)        # hardwired addresses: load, compare
        ok = all(ram.br('eq', ram.load(i), A) for i in range(m))
        hard = ram.steps
        ram = RAM(x, w=8 * width, allowed=SCAN_OK)        # one pointer: increment, load, compare
        ptr, ok2 = 0, True
        for i in range(m):
            if not ram.br('eq', ram.load(ptr), A):
                ok2 = False
                break
            ptr = ram.op('add', ptr, 1)
        assert ok == ok2 == (not flips)
        print(f'm={m}, {label}: hardwired check {hard} steps, pointer loop {ram.steps} steps; '
              'every instruction except add, load, eq-branch disabled')
    # little-endian layout: A and B agree on their 8 high-order bytes, so every integer between them does too
    high = lambda v: (v >> 64).to_bytes(8, 'little')
    lo, hi = min(A, B), max(A, B)
    assert high(A) == high(B) == b' 1 2 0\n ' and all(high(rng.randrange(lo, hi + 1)) == high(A) for _ in range(1000))
    print('A and B share the 8 high-order bytes', high(A), '(little-endian); so does every integer between them: a word')
    print('   between A and B still ends its own record, and a B word elsewhere stays the intact falsified clause.')
    print('fooling families inside {A,B}^m: two unsatisfiable files that share a B position have no satisfiable')
    print('   point between them, so a family of pairwise separated unsatisfiable files has pairwise disjoint')
    print('   B sets: at most m members; the satisfiable side has one member.  log2|F| <= log2 m.')
    # lattice points between the unsatisfiable files (B,A) and (A,B): (x, A+B-x).  Upper bound: count the
    # 8-digit names x for which A+B-x is again an 8-digit name in the same layout (digit DP on the low bytes;
    # names above the declared variable count would only lower the count).
    for na, nb in ((a, b), ('53817264', '46182735')):
        fa, fb = na.encode(), nb.encode()
        ways = {0: 1}
        for k in range(8):
            nxt = {}
            for borrow, cnt in ways.items():
                for xd in range(0x30, 0x3A):
                    if k == 0 and xd == 0x30:
                        continue
                    v = fa[k] + fb[k] - xd - borrow
                    nb2 = 0
                    if v < 0:
                        v, nb2 = v + 256, 1
                    if 0x30 <= v <= 0x39 and not (k == 0 and v == 0x30):
                        nxt[nb2] = nxt.get(nb2, 0) + cnt
            ways = nxt
        inside = ways.get(0, 0) - 2                       # minus the two endpoints x=a, x=b
        print(f'names {na}/{nb}: at most {inside} interior lattice points (x, A+B-x) of the segment between (B,A) and (A,B)')
        print('   have two well-formed 8-digit records; those are satisfiable files.  Needed: more than A(T,W):')
        for W in (100, 1000, 10 ** 4):
            T = 2 * W
            print(f'   W={W:6d}: A(T=2W, W) = {A_bound(T, W):12d}  -> {"possible" if inside > A_bound(T, W) else "fails"}')


# ----------------------------------------------------------------- G
def dpll(clauses):
    """Tiny complete SAT test; clauses are lists of (variable, negated) with arbitrary variable names."""
    clauses = [c for c in clauses if not any((v, not s) in c for v, s in c)]     # drop tautologies
    if not clauses:
        return True
    if any(not c for c in clauses):
        return False
    unit = next((c[0] for c in clauses if len(set(c)) == 1), None)
    v, s = unit if unit else clauses[0][0]
    for val in ((not s,) if unit else (True, False)):                            # literal (v, negated=s)
        rest = []
        for c in clauses:
            if any(cv == v and (not cs) == val for cv, cs in c):
                continue
            rest.append([(cv, cs) for cv, cs in c if cv != v])
        if dpll(rest):
            return True
    return False


def decode(words):
    return [[(x >> 1, bool(x & 1)) for x in words[i:i + 3]] for i in range(0, len(words), 3)]


PUBLIC = []
for y in (1, 2):                                          # force y1 and y2 false with dummies 3, 4
    for s3, s4 in product((0, 1), repeat=2):
        PUBLIC += [2 * y + 1, 6 + s3, 8 + s4]


def sat_member(a, b0, delta):
    words = list(PUBLIC)
    for i, ai in enumerate(a):
        lit = ((i + 1) << (b0 + delta + 2)) + 1 + (2 << delta) * ai              # odd: a negated variable
        words += [lit, 2, 4, lit + 1, 2, 4]
    return words


def complete_fallback(ram, W):
    """Complete decision for every file: learn signs and the equality pattern of the variables by counted
    instructions (at most 4W + W(W-1)/2), then answer from finite control."""
    words = [ram.load(i) for i in range(W)]
    var = [ram.op('shr', x, 1) for x in words]
    neg = [ram.br('ne', ram.op('and', x, 1), 0) for x in words]
    reps, ident = [], []
    for i in range(W):
        for j, r in enumerate(reps):
            if ram.br('eq', var[i], var[r]):
                ident.append(j)
                break
        else:
            reps.append(i)
            ident.append(len(reps) - 1)
    return dpll([[(ident[k], neg[k]) for k in range(i, i + 3)] for i in range(0, W, 3)])


def pair_solver(x, m, b0, delta, w, complete=False):
    """20-operation scan: sound certificates on the family and on its segment points; elsewhere None, or the
    verdict of the complete fallback when complete=True."""
    ram = RAM(x, w=w)

    def other():
        return (complete_fallback(ram, len(x)) if complete else None), ram.steps

    if not all(ram.br('eq', ram.load(i), PUBLIC[i]) for i in range(len(PUBLIC))):
        return other()
    all_good = True
    for i in range(m):
        base = len(PUBLIC) + 6 * i
        if not all(ram.br('eq', ram.load(base + k), v) for k, v in ((1, 2), (2, 4), (4, 2), (5, 4))):
            return other()
        lit, nxt = ram.load(base), ram.load(base + 3)
        if not ram.br('eq', ram.op('add', lit, 1), nxt):
            return other()
        if ram.br('eq', ram.op('and', lit, 1), 0):
            return False, ram.steps                       # (x_u or y1 or y2) and (not x_u or y1 or y2)
        slot = (i + 1) << (b0 + delta + 2)
        all_good &= ram.br('ge', lit, slot) and ram.br('lt', lit, slot + (1 << (b0 + delta + 1)))
    return (True, ram.steps) if all_good else other()


def section_G():
    print('== G. Binary 3-CNF, one literal per word (variable = word>>1, negated = word&1)')
    for m, b0, delta in ((1, 2, 1), (2, 2, 1), (2, 1, 2), (3, 1, 1)):
        D = 1 << delta
        fam = [sat_member(a, b0, delta) for a in product(range(1 << b0), repeat=m)]
        assert all(dpll(decode(p)) for p in fam)
        least, w = None, max(fam[-1]).bit_length() + 1
        for i, p in enumerate(fam):
            assert pair_solver(p, m, b0, delta, w)[0] is True
            for q in fam[:i]:
                g = 0
                for u, v in zip(p, q):
                    g = gcd(g, abs(u - v))
                unsat = 0
                for j in range(1, g):
                    y = [u + j * (v - u) // g for u, v in zip(p, q)]
                    truth = dpll(decode(y))
                    verdict = pair_solver(y, m, b0, delta, w)[0]
                    assert verdict is None or verdict == truth
                    unsat += not truth
                least = unsat if least is None else min(least, unsat)
        steps = pair_solver(fam[-1], m, b0, delta, w)[1]
        print(f'm={m} b0={b0} delta={delta}: W={len(fam[0])} words of {w - 1} bits, {len(fam)} satisfiable members; '
              f'fewest unsatisfiable lattice points inside a segment={least} >= D={D}; scan solver {steps} steps on a member')
        assert least >= D
    rng = random.Random(14)
    checked = worst = 0
    for m, b0, delta in ((1, 2, 1), (2, 2, 1)):
        fam = [sat_member(a, b0, delta) for a in product(range(1 << b0), repeat=m)]
        w = max(fam[-1]).bit_length() + 1
        for _ in range(1500):
            y = list(rng.choice(fam))
            for _ in range(rng.randrange(1, 6)):          # perturb words, often onto small or colliding values
                k = rng.randrange(len(y))
                y[k] = rng.choice((rng.randrange(1 << (w - 1)), rng.randrange(12), y[rng.randrange(len(y))] ^ 1))
            verdict, steps = pair_solver(y, m, b0, delta, w, complete=True)
            assert verdict == dpll(decode(y))
            checked += 1
            worst = max(worst, steps)
    print(f'with the complete fallback: correct on {checked} random perturbed files (worst {worst} steps; '
          'fallback bound 4W+W(W-1)/2)')
    print('thresholds of Theorem 1 (integer registers) for this family: W=6m+24 words of w bits')
    print('m, w, best b0, delta, W, N=W*w, T0, T0/W, T0/N, 20-operation scan 16m+48')
    for m in (10 ** 3, 10 ** 6):
        W = 6 * m + 24
        wj = 32
        while wj != 32 * (W * wj + 1).bit_length():       # the journal's rule w = 32*ceil(log2(N+2))
            wj = 32 * (W * wj + 1).bit_length()
        for w in (32, 64, 128, 256, wj):
            best = (0, 0, 0)
            for delta in range(4, 100):
                b0 = w - 1 - (m + 1).bit_length() - delta - 2
                if b0 < 1:
                    break
                t = T0(m * b0, W, 1 << delta, H_int)
                if t > best[0]:
                    best = (t, b0, delta)
            t, b0, delta = best
            print(f'{m:8d} {w:5d} {b0:5d} {delta:4d} {W:8d} {W * w:12d} {t:12d} {t / W:8.2f} {t / (W * w):7.4f} {16 * m + 48:9d}')
    m, b0, delta = 1000, 40, 20
    w = 1 + (m + 1).bit_length() + b0 + delta + 2
    rng = random.Random(14)
    p = sat_member([rng.randrange(1 << b0) for _ in range(m)], b0, delta)
    verdict, steps = pair_solver(p, m, b0, delta, w)
    q = list(p)
    k = len(PUBLIC) + 6 * rng.randrange(m)
    q[k] += 1
    q[k + 3] += 1
    verdict2, steps2 = pair_solver(q, m, b0, delta, w)
    assert verdict is True and verdict2 is False and steps == 16 * m + 48
    print(f'executed: m={m}, w={w}: member accepted in {steps} steps (16m+48); a neighbouring segment point rejected in {steps2}')


def main():
    section_F()
    section_G()
    print('all assertions passed')


if __name__ == '__main__':
    main()
