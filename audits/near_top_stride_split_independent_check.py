"""Independent check, written during review, of the q = 1 / q = 2^s split of Section 5 of
notes/length-dependent-markers-and-the-prologue-branch-classes.md.

Enumerates every one-instruction form op(a, b) with a, b in {0, n, w} U literals (|c| <= 12):
all 16 binary Boolean functions, add/sub/mul, comparisons (0/1), moves, and shl/shr/sar/rotl/rotr
with count operand from {0, n, w} U literals, including negative literal counts, under two count
rules ('modw': counts mod w for shifts and rotations; 'sat': rotations mod w, shifts by >= w give
0, sar gives sign fill).  At n = Q - m (w | n, m least > c_P), every odd form except the logical
right shifts and the right rotations is tested for q = 1 with |delta| <= 2^(s+1) * max(m, w, c_P).
This is the split as first stated.  Every failure it finds has a negative-literal count; at j a
power of two these are the left rotations by -c, which the corrected split counts as right
rotations by c (q = 2^c).
Run: python3 near_top_stride_split_independent_check.py   (under a second)
"""
import sys

def norm(a, Q):
    a %= Q
    return min(a, Q - a)

def run(j, sem, lits):
    w = 16 * j
    Q = 1 << w
    M = Q - 1
    cP = max(abs(c) for c in lits) + 1
    m = next(m for m in range(cP + 1, cP + 1 + 2 * w) if (Q - m) % w == 0)
    n = Q - m
    vals = {'0': 0, 'n': n, 'w': w}
    for c in lits:
        vals[str(c)] = c % Q
    names = list(vals)
    out = []  # (name, z, count_literal or None)
    def tosigned(x):
        return x - Q if x >= Q // 2 else x
    for a in names:
        for b in names:
            x, y = vals[a], vals[b]
            out.append((f'{a}+{b}', (x + y) & M, None))
            out.append((f'{a}-{b}', (x - y) & M, None))
            out.append((f'{a}*{b}', (x * y) & M, None))
            for f in range(16):  # all 16 binary Boolean functions, bitwise
                # f's truth table bit index = 2*xbit + ybit
                r = 0
                if f & 1: r |= (~x & ~y) & M
                if f & 2: r |= (~x & y) & M
                if f & 4: r |= (x & ~y) & M
                if f & 8: r |= (x & y) & M
                out.append((f'bool{f}({a},{b})', r, None))
            out.append((f'eq({a},{b})', int(x == y), None))
            out.append((f'ltu({a},{b})', int(x < y), None))
            out.append((f'lts({a},{b})', int(tosigned(x) < tosigned(y)), None))
            # shifts/rotations: data a, count b
            cnt = y
            lit = int(b) if b not in ('0', 'n', 'w') else None
            s_r = cnt % w
            rotr = ((x >> s_r) | (x << (w - s_r))) & M if s_r else x
            rotl = ((x << s_r) | (x >> (w - s_r))) & M if s_r else x
            if sem == 'modw':
                s_s = cnt % w
                shl = (x << s_s) & M
                shr = x >> s_s
                sar = (tosigned(x) >> s_s) & M
            else:
                shl = (x << cnt) & M if cnt < w else 0
                shr = x >> cnt if cnt < w else 0
                sar = (tosigned(x) >> min(cnt, w)) & M
            for nm, z in (('rotr', rotr), ('rotl', rotl), ('shl', shl), ('shr', shr), ('sar', sar)):
                out.append((f'{nm}({a},{b})', z, lit))
        out.append((f'mov({a})', vals[a], None))
    bad = []
    nodd = 0
    for name, z, lit in out:
        if z % 2 == 0:
            continue
        nodd += 1
        # s = |literal count| (the lemma states s for nonnegative literals; for a
        # negative literal we allow s = |c| as the most generous reading)
        s = abs(lit) if (lit is not None and 0 < abs(lit) < w) else 0
        bnd = (1 << (s + 1)) * max(m, w, cP)
        # Section 2.5 split: every form except logical right shifts and right
        # rotations is claimed to be a q = 1 form with |delta| = O_P(w).
        if name.startswith('shr(') or name.startswith('rotr('):
            continue
        ok = norm(z, Q) <= bnd
        if not ok:
            # best power-of-two q up to 2^24 for information
            best = min((norm((1 << s) * z, Q), s) for s in range(0, 25))
            bad.append((name, lit, best[1], best[0]))
    return w, m, nodd, bad

if __name__ == '__main__':
    lits = list(range(-12, 13))
    for sem in ('modw', 'sat'):
        for j in (8, 9, 13, 16, 17, 25, 32, 33, 64):
            w, m, nodd, bad = run(j, sem, lits)
            negcnt = [b for b in bad if b[1] is not None and b[1] < 0]
            other = [b for b in bad if not (b[1] is not None and b[1] < 0)]
            print(f'{sem:4s} j={j:3d} w={w:5d} m={m:5d} odd forms={nodd:6d} violating={len(bad):4d} '
                  f'(negative-literal count: {len(negcnt)}, other: {len(other)})')
            for b in (negcnt[:2] + other[:3]):
                print('     e.g.', b[0], 'best 2^s:', b[2], 'norm(2^s z) =', b[3], f'(~2^{b[3].bit_length()})')
