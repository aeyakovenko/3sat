#!/usr/bin/env python3
"""Second route for the three prologue-branch classes: the lengths below Q/2 (S_lo).

(1) For each witness family with an explicit length formula, list the family lengths over a
    parameter range, classify each by the standard width rule w = 16*ceil(log2(n+2)/16),
    Q = 2^w, into S_lo = {n < Q/2} or not, and check (i) the largest ratio of consecutive
    lengths (below 2^15 means the family cannot jump over the S_lo window of any width block)
    and (ii) that every width block in the range contains an S_lo member.
      - property-1 periodic even base of five-instruction-loops (exact formula of the
        journal audit dimacs_five_slot_layout.verified_family, reimplemented);
      - the read-only decimal family N = 1024 (j+1) 10^j;
      - the table-index family n ~ C (D+1) 2^t t^2 (D = 1, C = 64, byte-aligned);
      - the one-accumulator family N = 8 (2K ceil(log2(K+2))^2 + 64), K on a 1% grid.
(2) Regime lemma on S_lo: every comparison of two words from {0, n, w} and literals
    |c| <= 12 (unsigned and signed <, <=, =, both operand orders) is constant over sampled
    byte-aligned S_lo lengths n >= 2^20 at widths 32..256; over S_lo and S_hi together the
    signed tests of n are not constant (the reason for the gap).
Writes nothing.  Journal note: prologue-branches-are-fixed-jumps-at-each-length.md.
Usage: python3 -B prologue_branch_family_lengths_check.py   (about 4 s)
"""
from itertools import product
from fractions import Fraction

def width(n):
    return 16 * (((n + 1).bit_length() + 15) // 16)   # = 16*ceil(log2(n+2)/16)

def regime(n):
    w = width(n); Q = 1 << w
    return 'lo' if n < Q // 2 else 'hi'

def record(names, negative):           # as in audits/dimacs_five_slot_layout.py
    out = bytearray()
    for name, neg in zip(names, negative):
        if len(out) % 2 == 0:
            out.extend(b' ')
        out.extend(b'-' if neg else b' ')
        out.extend(str(name).encode('ascii'))
        out.extend(b' ')
    out.extend(b'0')
    if len(out) % 2 == 0:
        out.extend(b' ')
    out.extend(b'\n')
    return bytes(out)

def prop1_len(j):
    total = 10 ** j
    header = f'p cnf 20 {total}'.encode('ascii')
    header += (b' ' if len(header) % 2 == 0 else b'') + b'\n'
    pins = [record((var, 8, 20), (False, a, b)) for var in (2, 4, 6) for a, b in product((False, True), repeat=2)]
    base = record((2, 4, 6), (False, False, False))
    prefix = header + b''.join(pins)
    return 8 * (len(prefix) + (total - len(pins)) * len(base))

def ilog2sq(K):
    b = (K + 2).bit_length()          # ceil(log2(K+2)) up to +1, monotone
    return b * b

def kgrid():
    K = 100
    while K.bit_length() < 1290:
        yield K
        K += max(1, K // 100)

families = {
    'property-1 base (FL), j=3..400': [prop1_len(j) for j in range(3, 401)],
    'RO decimal N=1024(j+1)10^j, j=3..400': [1024 * (j + 1) * 10 ** j for j in range(3, 401)],
    'table n~64*2*2^t*t^2, t=8..1300': [8 * ((64 * 2 * (1 << t) * t * t + 7) // 8) for t in range(8, 1301)],
    'one-accumulator N=8(2K*ceil(log2(K+2))^2+64), K on a 1% grid': sorted(set(
        8 * (2 * K * ilog2sq(K) + 64) for K in kgrid())),
}
print('(1) family lengths against the S_lo window of each width block')
for name, ns in families.items():
    ns = sorted(ns)
    maxratio = max(Fraction(b, a) for a, b in zip(ns, ns[1:]))
    blocks = {}
    for n in ns:
        blocks.setdefault(width(n), []).append(regime(n))
    ws = sorted(blocks)
    inner = ws[1:-1]                               # blocks fully inside the sampled range
    empty = [w for w in inner if 'lo' not in blocks[w]]
    lo = sum(r == 'lo' for v in blocks.values() for r in v)
    print(f'  {name}: members {len(ns)}, in S_lo {lo}, widths {ws[0]}..{ws[-1]}, '
          f'max consecutive ratio {float(maxratio):.4g} (< 2^15: {maxratio < 2**15}), '
          f'inner width blocks without an S_lo member: {len(empty)} of {len(inner)}')

print('(2) prologue tests on S_lo')
lits = list(range(-12, 13))
def tests(n):
    w = width(n); Q = 1 << w
    ops = {'0': 0, 'n': n, 'w': w}
    for c in lits:
        ops[f'lit{c}'] = c % Q
    sgn = lambda v: v - Q if v >= Q // 2 else v
    out = {}
    for (a, va), (b, vb) in product(ops.items(), repeat=2):
        out[(a, b, 'ult')] = va < vb
        out[(a, b, 'ule')] = va <= vb
        out[(a, b, 'slt')] = sgn(va) < sgn(vb)
        out[(a, b, 'sle')] = sgn(va) <= sgn(vb)
        out[(a, b, 'eq')] = va == vb
    return out
samples_lo, samples_all = [], []
for w in (32, 48, 64, 128, 256):
    Q = 1 << w
    lo_start = max(1 << 20, (1 << (w - 16)))
    pts = [lo_start, lo_start + 8, Q // 4, Q // 2 - 8, (Q // 2 - 8) // 3 * 2]
    pts = [n - n % 8 for n in pts]
    pts = [n for n in pts if width(n) == w and n >= 1 << 20]
    samples_lo += [n for n in pts if regime(n) == 'lo']
    samples_all += pts + [Q // 2, Q // 2 + 8, Q - 64, Q - 16]
ref = tests(samples_lo[0])
nonconst_lo = {k for n in samples_lo for k, v in tests(n).items() if v != ref[k]}
ref2 = tests(samples_all[0])
nonconst_all = {k for n in samples_all for k, v in tests(n).items() if v != ref2[k]}
print(f'  S_lo sample lengths {len(samples_lo)} (widths 32..256), tests per length {len(ref)}, '
      f'tests not constant on S_lo: {len(nonconst_lo)}')
print(f'  with S_hi and near-top lengths added ({len(samples_all)} lengths): tests not constant: '
      f'{len(nonconst_all)}, e.g. {sorted(nonconst_all)[:4]}')
