#!/usr/bin/env python3
"""Mechanical coverage check of the five-slot case split.

Input: five_slot_control_graph_signatures.txt, the output of
five_slot_control_graphs.cpp (every control graph with <= 5 stored nodes and
<= 2 branch sites; b >= 3 is handled by the type count below), read from this
script's directory unless --signatures FILE is given.  Then every operand
allocation of the surviving typed signatures is generated and each class is
matched against one predicate per cited sentence of the journal's case split.
There is no default branch: a class no predicate matches is reported as
UNCOVERED.

Run: python3 five_slot_case_split_coverage.py [--drop RULE] [--signatures FILE] [--out DIR]
Prints the coverage summary.  With --out DIR it also writes coverage_typed.txt,
coverage_operands.txt and coverage_summary.txt (with a .drop-RULE suffix when a
rule is dropped) to DIR.
"""
import itertools, sys, collections, re, os, io

DROP = set()
if '--drop' in sys.argv:
    DROP.add(sys.argv[sys.argv.index('--drop') + 1])
SUFFIX = ('.drop-' + '-'.join(sorted(DROP))) if DROP else ''
OUT = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
SIGNATURES = (sys.argv[sys.argv.index('--signatures') + 1] if '--signatures' in sys.argv else
              os.path.join(os.path.dirname(os.path.abspath(__file__)), 'five_slot_control_graph_signatures.txt'))

N5 = 'notes/five-instructions-cannot-decide-dimacs-sat.md'
FL = 'notes/five-instruction-loops-on-dimacs-sat.md'
WR = 'notes/writable-five-slots-without-a-clock.md'
RO = 'notes/read-only-five-instructions-on-ordinary-sat.md'
R1 = 'notes/read-only-ram-with-one-arithmetic-site.md'
AP = 'notes/adaptive-five-slot-prefixes-without-a-clock.md'

# ---------------------------------------------------------------- type layer
TYPE_RULES = []   # (name, citation, level, predicate(sig))

def trule(name, cite, level):
    def deco(f):
        TYPE_RULES.append((name, cite, level, f))
        return f
    return deco

def counts(sig):
    allt = sig['cyc'] + sig['pro'] + sig['ext'] + sig['side']
    return allt.count('L'), allt.count('N'), allt.count('S')

@trule('T-noLOAD', WR + ' para 2 ("Without a LOAD the answer is independent of the file")', 'A')
def _(s):
    L, N, S = counts(s); return L == 0

@trule('T-noNUM', WR + ' para 2; ' + FL + ' #the-control-graph ("no value-making operation ... bounded initial alphabet")', 'A')
def _(s):
    L, N, S = counts(s); return N == 0

@trule('T-noBranchOnCycle', N5 + ' step 1 (halting runs never enter a branch-free cycle, so every site runs at most once: acyclic)', 'A-implied')
def _(s):
    return s['brOnCycle'] == 0

@trule('T-LOADoffCycle', WR + ' para 2 ("With the sole LOAD ... off cycle"); ' + N5 + ' step 1', 'A')
def _(s):
    return 'L' not in s['cyc']

@trule('T-oneNUM-readonly', R1 + ' (any number of LOADs and branches, one numerical site, no STORE, any control)', 'A')
def _(s):
    L, N, S = counts(s); return S == 0 and N == 1

@trule('T-NUMoffCycle-writable', WR + ' para 2 ("sole ... numerical site off cycle"); ' + FL + ' #the-control-graph', 'A')
def _(s):
    L, N, S = counts(s); return S >= 1 and N >= 1 and 'N' not in s['cyc'] and L >= 1

# The remaining typed signatures need the operand layer; they are tagged here.
def operand_family(s):
    L, N, S = counts(s)
    cyc = s['cyc']
    if (L, N, S) == (1, 1, 1) and sorted(cyc) == ['L', 'N', 'S']:
        return 'W-cyc'
    if (L, N, S) == (1, 1, 1) and sorted(cyc) == ['L', 'N'] and s['pro'] == 'S':
        return 'W-proS'
    if (L, N, S) == (1, 1, 1) and sorted(cyc) == ['L', 'N'] and (s['ext'] == 'S' or s['side'] == 'S'):
        return 'W-exitS'
    if (L, N, S) == (1, 2, 0) and sorted(cyc) == ['L', 'N', 'N']:
        return 'R2-cyc'
    if (L, N, S) == (1, 2, 0) and sorted(cyc) == ['L', 'N']:
        return 'R2-offN:' + ('pro' if 'N' in s['pro'] else 'ext/side')
    if (L, N, S) == (1, 2, 0) and cyc == 'L':
        return 'R2-offNN'
    return None

# --------------------------------------------------------------- operand layer
OPS = {  # opcode class -> arity ; role order for shift/rot = (data, count); sub = (o1 - o2)
    'add': 2, 'sub': 2, 'mul': 2, 'bool2': 2, 'cmp': 2,
    'shift': 2, 'rot': 2, 'bool1': 1, 'mov': 1,
}
ARITH = {'add', 'sub', 'mul'}
FIXED_W = ['ie', 'io', 'r0', 'rn', 'rw']   # even literal, odd literal, zero reg, n reg, w reg
def is_fixed(o): return o not in ('x', 'p', 'a', 'b', 'y')
def is_odd_fixed(o): return o == 'io'

def nums(syms):
    for op, ar in OPS.items():
        for ops in itertools.product(syms, repeat=ar):
            yield (op, ops)

OPR_RULES = collections.defaultdict(list)   # family -> [(name, cite, level, pred)]
def orule(family, name, cite, level):
    def deco(f):
        OPR_RULES[family].append((name, cite, level, f))
        return f
    return deco

# ---- writable, all three data sites on the cycle -------------------------
# class c: dict(coinc, AL, num=(op, ops), AS, VS, order in {'LNS','LSN'})
def mut_ops(c): return [o for o in c['num'][1] if not is_fixed(o)]

@orule('W-cyc', 'W1-fixedLOAD', FL + ' #the-control-graph ("A LOAD at such a fixed address fails the required-read test")', 'A')
def _(c): return is_fixed(c['AL'])

# coincident destinations (single mutable register r named x)
@orule('W-cyc', 'W2a-coinc-store-after-ALU', AP + ' #coincident-register-destinations bullet 1', 'A')
def _(c): return c['coinc'] and c['AL'] == 'x' and c['AS'] == 'x' and c['order'] == 'LNS'
@orule('W-cyc', 'W2b-coinc-store-between', AP + ' #coincident-register-destinations bullet 2', 'A')
def _(c): return c['coinc'] and c['AL'] == 'x' and c['AS'] == 'x' and c['order'] == 'LSN'
@orule('W-cyc', 'W2c-coinc-fixed-store', AP + ' #coincident-register-destinations bullet 3', 'A')
def _(c): return c['coinc'] and c['AL'] == 'x' and is_fixed(c['AS'])

# distinct, self-addressed LOAD x <- M[x]
@orule('W-cyc', 'W3a-self-store-at-x', FL + ' #an-address-bound ("a STORE at x between successive loads destroys the next original")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'x' and c['AS'] == 'x'
@orule('W-cyc', 'W3b-self-store-at-p-payload-x-or-fixed', FL + ' #an-address-bound ("STORE is at y with payload x or a fixed value")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'x' and c['AS'] == 'p' and (c['VS'] == 'x' or is_fixed(c['VS']))
@orule('W-cyc', 'W3c-self-store-at-p-payload-p', FL + ' #an-address-bound ("If it writes y, a modified cell contains its own address")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'x' and c['AS'] == 'p' and c['VS'] == 'p'
@orule('W-cyc', 'W3d-self-fixed-scratch', WR + ' #one-fixed-scratch-address para 3 (self-addressed LOAD, distinct numerical destination)', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'x' and is_fixed(c['AS'])

# distinct, LOAD x <- M[p]
@orule('W-cyc', 'W4-fixed-scratch-two-query', WR + ' #one-fixed-scratch-address paras 1-2,4', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and is_fixed(c['AS'])
@orule('W-cyc', 'W5-raw-word-table', WR + ' #writing-through-the-raw-word', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and c['AS'] == 'x' and (c['VS'] == 'x' or is_fixed(c['VS']))

def ignores_p(c): return 'p' not in c['num'][1]
@orule('W-cyc', 'W6-const-cursor', N5 + ' step 1 (cursor takes <= 2 values; loop reads <= 2 addresses)', 'A-implied')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and len(mut_ops(c)) == 0
@orule('W-cyc', 'W6a-fx-store-p-before-load', WR + ' #other-store-operands bullet 2 ("STORE through p before its LOAD ... destroys")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and ignores_p(c) and c['AS'] == 'p' and c['order'] == 'LNS'
@orule('W-cyc', 'W6b-fx-writeback', WR + ' #other-store-operands bullet 2 ("raw writeback ... two-query argument")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and ignores_p(c) and c['AS'] == 'p' and c['order'] == 'LSN' and c['VS'] == 'x'
@orule('W-cyc', 'W6c-fx-fixed-payload', WR + ' #other-store-operands bullet 2 ("fixed payload restricts regular addresses to f(H u {c})")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and ignores_p(c) and c['AS'] == 'p' and c['order'] == 'LSN' and is_fixed(c['VS'])
@orule('W-cyc', 'W6d-fx-self-mark', AP + ' row "Mark the address read"', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and ignores_p(c) and c['AS'] == 'p' and c['order'] == 'LSN' and c['VS'] == 'p'
@orule('W-cyc', 'W6e-fx-old-cursor-reverse-link', 'notes/unary-reverse-links-on-an-even-dimacs-base.md (requires f to use x)', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and ignores_p(c) and 'x' in c['num'][1] and c['AS'] == 'x' and c['VS'] == 'p' and c['order'] == 'LSN'
@orule('W-cyc', 'W6f-fx-updated-cursor-mark-value', AP + ' row "Mark the value read"', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and ignores_p(c) and c['AS'] == 'x' and c['VS'] == 'p' and c['order'] == 'LNS'

def p_only(c):
    ops = c['num'][1]; return 'p' in ops and 'x' not in ops
def odd_translation(c):
    op, ops = c['num']
    if op == 'add' and sorted(ops, key=str) in (['io', 'p'], ['p', 'io']) and ops.count('p') == 1:
        return True
    if op == 'sub' and ops[0] == 'p' and ops[1] == 'io':
        return True
    return False
@orule('W-cyc', 'W7-bnd-nontranslation', FL + ' #which-operation-can-generate-the-addresses (constant, copy, d-y, y-y, doubling, odd/even multiplier, squaring, bitwise, shifts, rotations, comparisons, even translation)', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and p_only(c) and not odd_translation(c)
@orule('W-cyc', 'W7a-unshifted-crossed-scan', 'notes/unshifted-crossed-scan-without-a-clock.md', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and odd_translation(c) and c['AS'] == 'x' and c['VS'] == 'p' and c['order'] == 'LSN'
@orule('W-cyc', 'W7b-shifted-crossed-scan', 'notes/arbitrary-stride-private-sign-erasure.md', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and odd_translation(c) and c['AS'] == 'x' and c['VS'] == 'p' and c['order'] == 'LNS'
@orule('W-cyc', 'W7c-translation-store-p-before-load', WR + ' #other-store-operands bullet 3 ("Through p, a STORE before its LOAD destroys")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and odd_translation(c) and c['AS'] == 'p' and c['order'] == 'LNS'
@orule('W-cyc', 'W7d-translation-stable-three-periods', WR + ' #other-store-operands bullet 3 (writeback/self-mark/fixed mark, three periods, communication)', 'B')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and odd_translation(c) and c['AS'] == 'p' and c['order'] == 'LSN'

def both_px(c):
    ops = c['num'][1]; return 'p' in ops and 'x' in ops
@orule('W-cyc', 'W8a-both-nonarith-bounded', WR + ' #other-store-operands bullet 4 (shifts, rotations, bitwise, comparisons: bounded palette)', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and both_px(c) and c['num'][0] in ('bool2', 'shift', 'rot', 'cmp')
@orule('W-cyc', 'W8b-both-arith-even', WR + ' #other-store-operands bullet 4 ("keep all data even ... STORE copies a register or an even fixed word")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and both_px(c) and c['num'][0] in ARITH and not is_odd_fixed(c['VS'])
@orule('W-cyc', 'W8c1-both-odd-marker-p-before-load', WR + ' #other-store-operands bullet 4 ("Through p before its LOAD it destroys originals")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and both_px(c) and c['num'][0] in ARITH and is_odd_fixed(c['VS']) and c['AS'] == 'p' and c['order'] == 'LNS'
@orule('W-cyc', 'W8c2-both-mul-odd-marker', WR + ' #other-store-operands bullet 4 ("multiplication preserves the evenness of p")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and both_px(c) and c['num'][0] == 'mul' and is_odd_fixed(c['VS']) and c['AS'] == 'p' and c['order'] == 'LSN'
@orule('W-cyc', 'W8c3-both-additive-odd-marker', 'notes/odd-self-marked-cursors-without-a-clock.md (p+x, p-x, x-p with M[p]<-c after the read)', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p' and both_px(c) and c['num'][0] in ('add', 'sub') and is_odd_fixed(c['VS']) and c['AS'] == 'p' and c['order'] == 'LSN'

def gen_wcyc():
    for coinc in (True, False):
        regs = ['x'] if coinc else ['x', 'p']
        syms = regs + FIXED_W
        for AL in syms:
            for num in nums(syms):
                for AS in syms:
                    for VS in syms:
                        for order in ('LNS', 'LSN'):
                            yield dict(coinc=coinc, AL=AL, num=num, AS=AS, VS=VS, order=order)

# ---- writable with the STORE in the prologue (runs once, before every LOAD) ---
@orule('W-proS', 'WP-fixedLOAD', FL + ' #the-control-graph', 'A')
def _(c): return is_fixed(c['AL'])
@orule('W-proS', 'WP-distinct-two-query', WR + ' #one-fixed-scratch-address para 5 ("In the distinct-register x<-M[p] case the preceding two-query argument applies directly")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'p'
@orule('W-proS', 'WP-self-addressed', WR + ' #one-fixed-scratch-address para 5 ("A self-addressed x<-M[x] ... cannot reach a chosen site")', 'A')
def _(c): return (not c['coinc']) and c['AL'] == 'x'
@orule('W-proS', 'WP-coinc-two-query', WR + ' #one-fixed-scratch-address para 2 ("If there is only one mutable register, its post-LOAD value is likewise fixed by the reply"); not named in para 5', 'A-implied')
def _(c): return c['coinc'] and c['AL'] == 'x'

def gen_wpro():
    for coinc in (True, False):
        regs = ['x'] if coinc else ['x', 'p']
        syms = regs + FIXED_W
        for AL in syms:
            for num in nums(syms):
                for AS in FIXED_W:          # prologue: all registers hold initial values
                    for VS in FIXED_W:
                        yield dict(coinc=coinc, AL=AL, num=num, AS=AS, VS=VS, order='-')

# ---- writable with the STORE after the cycle (exit or side arm) ---------------
@orule('W-exitS', 'WE-store-never-precedes-a-LOAD', WR + ' #one-fixed-scratch-address para 5 ("cannot influence a subsequent LOAD") + ' + R1, 'A-implied')
def _(c): return True
def gen_wexit():
    yield dict(note='STORE after the last LOAD: delete it, read-only one-NUM program remains')

# ---- read-only, both numerical sites on the cycle ----------------------------
# registers: x = LOAD dest; a = dest of the first NUM after the LOAD in cyclic
# order, b = dest of the second; aliasing patterns enumerated.
RO_FIXED = ['k0', 'k1']   # fixed word with low pair 00 (0, n, w, literal) / other literal
def ro_patterns():
    # (dest of first NUM, dest of second NUM) in canonical names
    yield ('x', 'x'); yield ('x', 'a'); yield ('a', 'x'); yield ('a', 'a'); yield ('a', 'b')

def gen_r2():
    for da, db in ro_patterns():
        regs = sorted(set(['x', da, db]))
        syms = regs + RO_FIXED
        for AL in syms:
            for na in nums(syms):
                for nb in nums(syms):
                    yield dict(da=da, db=db, regs=regs, AL=AL, na=na, nb=nb)

def r2_split(c):
    """return (p_update, y_update) naming for the 3-register cursor form."""
    p = c['AL']
    if c['da'] == p: Fp, Gy, y = c['na'], c['nb'], c['db']
    else: Fp, Gy, y = c['nb'], c['na'], c['da']
    return p, y, Fp, Gy

@orule('R2-cyc', 'R-fixedLOAD', RO + ' #control-and-register-aliases ("cannot be an immediate or a register constant")', 'A')
def _(c): return is_fixed(c['AL'])
@orule('R2-cyc', 'R-2reg-distinct-address', RO + ' #control-and-register-aliases ("a specified address fixes the latter ... one live context")', 'A')
def _(c): return len(c['regs']) <= 2 and c['AL'] != 'x' and not is_fixed(c['AL'])
@orule('R2-cyc', 'R-2reg-self-addressed', RO + ' #control-and-register-aliases ("When the LOAD takes its own destination as address ... M<=hQ")', 'A')
def _(c): return len(c['regs']) <= 2 and c['AL'] == 'x'
@orule('R2-cyc', 'R-3reg-self-addressed', RO + ' #control-and-register-aliases ("a self-addressed LOAD that is never a numerical destination")', 'A')
def _(c): return len(c['regs']) == 3 and c['AL'] == 'x'

def three_cursor(c): return len(c['regs']) == 3 and c['AL'] in ('a', 'b')
@orule('R2-cyc', 'R-case1-cursor-ignores-p', RO + ' #all-operand-choices case 1', 'A')
def _(c):
    if not three_cursor(c): return False
    p, y, Fp, Gy = r2_split(c); return p not in Fp[1]
@orule('R2-cyc', 'R-case2-public-unary-orbit', RO + ' case 2 -> notes/one-accumulator-scan-without-a-clock.md #any-unary-orbit-of-public-read-addresses', 'A')
def _(c):
    if not three_cursor(c): return False
    p, y, Fp, Gy = r2_split(c); return p in Fp[1] and all(o == p or is_fixed(o) for o in Fp[1])
@orule('R2-cyc', 'R-case3-cursor-uses-p-and-x', RO + ' case 3 (residues mod 4, bounded shifts/moves/comparisons)', 'A')
def _(c):
    if not three_cursor(c): return False
    p, y, Fp, Gy = r2_split(c); return p in Fp[1] and 'x' in Fp[1]
def case4(c):
    if not three_cursor(c): return None
    p, y, Fp, Gy = r2_split(c)
    if p in Fp[1] and y in Fp[1]: return p, y, Fp, Gy
    return None
@orule('R2-cyc', 'R-case4a-y-ignores-old-y', RO + ' case 4 ("If the update to y ignores its old value ... M<=hQ")', 'A')
def _(c):
    t = case4(c); return bool(t) and t[1] not in t[3][1]
@orule('R2-cyc', 'R-case4b-both-ignore-x-XOR', RO + ' case 4 ("If both numerical sites ignore x ... XOR of two private bits")', 'A')
def _(c):
    t = case4(c); return bool(t) and 'x' not in t[2][1] and 'x' not in t[3][1]
def case4c(c):
    t = case4(c)
    if not t: return None
    p, y, Fp, Gy = t
    if set(Gy[1]) == {y, 'x'}: return t
    return None
@orule('R2-cyc', 'R-case4c-G-bounded', RO + ' para after case 4 (G bitwise / shift / rotation / comparison: few y values)', 'A')
def _(c):
    t = case4c(c); return bool(t) and t[3][0] in ('bool2', 'shift', 'rot', 'cmp')
@orule('R2-cyc', 'R-case4c-G-arith-F-arith-or-bitwise', RO + ' ("If F is arithmetic, the cursor retains low pair 00. If F is any bitwise function ... equal low bits")', 'A')
def _(c):
    t = case4c(c); return bool(t) and t[3][0] in ARITH and t[2][0] in ARITH | {'bool2'}
@orule('R2-cyc', 'R-case4c-G-arith-F-cmp', RO + ' ("a comparison yields at most two addresses")', 'A')
def _(c):
    t = case4c(c); return bool(t) and t[3][0] in ARITH and t[2][0] == 'cmp'
@orule('R2-cyc', 'R-case4c-G-arith-F-shift-p-data', RO + ' ("A shift or rotation with p as the data again has only O(w) descendants")', 'A')
def _(c):
    t = case4c(c); return bool(t) and t[3][0] in ARITH and t[2][0] in ('shift', 'rot') and t[2][1][0] == t[0]
@orule('R2-cyc', 'R-case4c-G-arith-F-shift-p-count', RO + ' ("old p supplies the shift or rotation count ... M<=(w+1)Qh")', 'A')
def _(c):
    t = case4c(c); return bool(t) and t[3][0] in ARITH and t[2][0] in ('shift', 'rot') and t[2][1][1] == t[0] and t[2][1][0] == t[1]

# ---- read-only with one numerical site off the cycle ---------------------------
@orule('R2-offN', 'RO-fixedLOAD', RO + ' #control-and-register-aliases', 'A')
def _(c): return is_fixed(c['AL'])
@orule('R2-offN', 'RO-2reg-distinct-address', RO + ' ("These cases cover off-cycle numerical sites as well"): one live context', 'A')
def _(c): return c['AL'] == 'a' and c['dcyc'] == 'a'
@orule('R2-offN', 'RO-2reg-self-addressed', RO + ' ("These cases cover off-cycle numerical sites as well"): M<=hQ', 'A')
def _(c): return c['AL'] == 'x'
def gen_r2off():
    # cycle NUM writes dcyc in {x, a}; the off-cycle NUM wrote z (fixed during the cycle, any value)
    for dcyc in ('x', 'a'):
        regs = sorted(set(['x', dcyc]))
        syms = regs + ['z'] + RO_FIXED
        for AL in syms:
            if AL == 'a' and dcyc != 'a': continue
            for n in nums(syms):
                yield dict(dcyc=dcyc, AL=AL, num=n)

# ---- read-only with both numerical sites off the cycle (cycle = LOAD + branches) ---
@orule('R2-offNN', 'RNN-fixedLOAD', RO + ' #control-and-register-aliases (LOAD address constant throughout the cycle)', 'A')
def _(c): return is_fixed(c['AL'])
@orule('R2-offNN', 'RNN-1reg-self-addressed', RO + ' #control-and-register-aliases (<=2 varying registers, self-addressed; "These cases cover off-cycle numerical sites as well")', 'A')
def _(c): return c['AL'] == 'x'
def gen_r2offnn():
    for AL in ['x', 'z1', 'z2'] + RO_FIXED:   # z1, z2: registers written once off the cycle
        yield dict(AL=AL)

GEN = {'W-cyc': gen_wcyc, 'W-proS': gen_wpro, 'W-exitS': gen_wexit, 'R2-cyc': gen_r2,
       'R2-offN:pro': gen_r2off, 'R2-offN:ext/side': gen_r2off, 'R2-offNN': gen_r2offnn}
FAM_RULES = {'R2-offN:pro': 'R2-offN', 'R2-offN:ext/side': 'R2-offN'}

def main():
    sigs = []
    for line in open(SIGNATURES):
        if not line.startswith('SIG '): continue
        m = re.match(r'SIG cyc=(\S*) pro=(\S*) ext=(\S*) side=(\S*) brOnCycle=(\d) : (\d+)', line)
        cyc, pro, ext, side, br, cnt = m.groups()
        sigs.append(dict(cyc=cyc, pro=pro, ext=ext, side=side, brOnCycle=int(br), count=int(cnt)))
    out = io.StringIO()
    fams = collections.Counter(); uncovered_typed = []
    rule_hits = collections.Counter()
    for s in sigs:
        hits = [r[0] for r in TYPE_RULES if r[0] not in DROP and r[3](s)]
        fam = None
        if not hits:
            fam = operand_family(s)
        for h in hits: rule_hits[h] += 1
        tag = ','.join(hits) if hits else ('OPERAND-LAYER:' + fam if fam else 'UNCOVERED')
        if not hits and not fam: uncovered_typed.append(s)
        if fam: fams[fam] += s['count']
        out.write('cyc=%s pro=%s ext=%s side=%s brOnCycle=%d graphs*typings=%d -> %s\n' % (s['cyc'], s['pro'], s['ext'], s['side'], s['brOnCycle'], s['count'], tag))
    typed_text = out.getvalue()
    # b >= 3 branches with <= 5 stored sites leave <= 2 data sites
    b3 = []
    for d in range(0, 3):
        for ms in itertools.combinations_with_replacement('LNS', d):
            s = dict(cyc=''.join(ms), pro='', ext='', side='', brOnCycle=1)
            L, N, S = counts(s)
            hits = [r[0] for r in TYPE_RULES if r[0] not in DROP and r[0] in ('T-noLOAD', 'T-noNUM', 'T-oneNUM-readonly') and r[3](s)]
            b3.append((''.join(ms), hits))
    # operand layer
    ores = {}
    oout = io.StringIO()
    for fam in sorted(fams):
        rules = [r for r in OPR_RULES[FAM_RULES.get(fam, fam)] if r[0] not in DROP]
        tot = 0; unc = []; hitc = collections.Counter(); multi = 0
        for c in GEN[fam]():
            tot += 1
            hits = [r[0] for r in rules if r[3](c)]
            for h in hits: hitc[h] += 1
            if not hits: unc.append(c)
            if len(hits) > 1: multi += 1
        ores[fam] = (tot, unc, hitc, multi, rules)
        oout.write('## family %s: %d operand classes, %d uncovered, %d covered by >1 rule\n' % (fam, tot, len(unc), multi))
        for r in rules:
            oout.write('  %-40s level %-9s hits %7d   %s\n' % (r[0], r[2], hitc[r[0]], r[1]))
        for c in unc[:200]:
            oout.write('  UNCOVERED %r\n' % (c,))
    operands_text = oout.getvalue()
    f = io.StringIO()
    f.write('dropped rules: %s\n' % (sorted(DROP) or 'none'))
    f.write('typed signatures (b_R=2): %d; uncovered at type level: %d\n' % (len(sigs), len(uncovered_typed)))
    for s in uncovered_typed: f.write('  UNCOVERED-TYPED %r\n' % s)
    f.write('type-rule hits (signatures): %s\n' % dict(rule_hits))
    f.write('type rules never firing: %s\n' % [r[0] for r in TYPE_RULES if r[0] not in DROP and rule_hits[r[0]] == 0])
    f.write('operand families reached (graph*typing counts): %s\n' % dict(fams))
    f.write('b>=3 data multisets (<=2 data sites): %s\n' % b3)
    f.write('b>=3 uncovered: %s\n' % [m for m, h in b3 if not h])
    for fam, (tot, unc, hitc, multi, rules) in sorted(ores.items()):
        f.write('operand family %s: classes %d, uncovered %d, multiply-covered %d, rules never firing %s\n' % (fam, tot, len(unc), multi, [r[0] for r in rules if hitc[r[0]] == 0]))
    summary_text = f.getvalue()
    if OUT:
        for name, text in (('coverage_typed', typed_text), ('coverage_operands', operands_text),
                           ('coverage_summary', summary_text)):
            with open(os.path.join(OUT, '%s%s.txt' % (name, SUFFIX)), 'w') as g:
                g.write(text)
    print(summary_text)

if __name__ == '__main__':
    main()
