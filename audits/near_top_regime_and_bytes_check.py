"""Three small checks for notes/length-dependent-markers-and-the-prologue-branch-classes.md.
Run: python3 near_top_regime_and_bytes_check.py   (about 3 s)

(1) Prologue-computable odd markers at near-top lengths n = Q - m have
    q*z = delta (mod Q) with q in {1, 2^s} and |delta| <= 2^(s+1)*max(m, w, c_P),
    s = |count literal| for shifts and rotations with a literal count, else 0.
    Every one-instruction form op(a, b), a, b in {0, n, w} and literals |c| <= 12
    (c_P = 12): add, sub, mul, all 16 bitwise Boolean functions, comparisons, moves,
    and shifts (logical, arithmetic, left) and rotations whose count is a literal
    (positive or negative) or a register (0, n, w), under two count rules
    (everything mod w; or saturating shifts with rotations mod w).  Widths
    w = 16*j for j in {8, 16, 32, 64} (powers of two) and {9, 13, 17, 25};
    m = m0 + w*t, t < 4, m0 the least m > c_P with w | Q - m.  The lemma claims
    no violation at powers of two, and none at other j unless the count is a
    negative literal.
(2) Band avoidance at a large width: no word with all bytes in [9, 126] lies
    within Delta = 2*L + 2*q*|delta| of a nonzero multiple of Q/2^s, s <= 8,
    once w > (2/9)*256^2.  Checked on adversarial words (top byte equal to the
    band's top byte, next byte 9 or 126, rest extreme) at w = 14592.
(3) Regime split of the read-only decimal family N = 8*128*(j+1)*10^j: how many
    j in [20, 400) have N < Q/2 (lower half of the width block) vs N >= Q/2.
No files are written.
"""
import sys

def width(n):
    import math
    # w = 16*ceil(log2(n+2)/16), exact with integers
    b = (n + 2 - 1).bit_length()  # ceil(log2(n+2)) for n+2 not a power of 2 handled below
    if (n + 2) & (n + 1) == 0:  # n+2 is a power of two
        b = (n + 2).bit_length() - 1
    return 16 * ((b + 15) // 16)

def norm(a, Q):
    a %= Q
    return min(a, Q - a)

BOOL16 = [tuple((f >> k) & 1 for k in range(4)) for f in range(16)]  # outputs for (x,y)=(0,0),(0,1),(1,0),(1,1)


def bitwise(f, x, y, Q):
    mask = Q - 1
    nx, ny = (~x) & mask, (~y) & mask
    r = 0
    if f[0]:
        r |= nx & ny
    if f[1]:
        r |= nx & y
    if f[2]:
        r |= x & ny
    if f[3]:
        r |= x & y
    return r & mask


def shift_forms(x, cnt, w, Q, rule):
    """Shifts and rotations of x by the word cnt.  Rotations use cnt mod w.
    rule 'mod': shifts also use cnt mod w; rule 'sat': shifts by cnt >= w saturate."""
    mask = Q - 1
    signed = x - Q if x >= Q // 2 else x
    r = cnt % w
    out = {'rotr': ((x >> r) | (x << (w - r))) & mask if r else x,
           'rotl': ((x << r) | (x >> (w - r))) & mask if r else x}
    if rule == 'mod' or cnt < w:
        e = r if rule == 'mod' else cnt
        out['shr'] = x >> e
        out['shl'] = (x << e) & mask
        out['sar'] = (signed >> e) & mask
    else:
        out['shr'] = 0
        out['shl'] = 0
        out['sar'] = (signed >> w) & mask  # 0 or Q-1
    return out


def forms(n, w, Q, lits):
    """Every one-instruction value op(a, b), a, b in {0, n, w} and literals.
    Yields (name, z, s, negative_count) where s = |count literal| for a shift or
    rotation with a literal count, else 0."""
    vals = {'0': 0, 'n': n, 'w': w}
    for c in lits:
        vals[str(c)] = c % Q
    names = list(vals)
    for a in names:
        x = vals[a]
        yield f'mov({a})', x, 0, False
        for b in names:
            y = vals[b]
            yield f'{a}+{b}', (x + y) % Q, 0, False
            yield f'{a}-{b}', (x - y) % Q, 0, False
            yield f'{a}*{b}', (x * y) % Q, 0, False
            for k, f in enumerate(BOOL16):
                yield f'bool{k}({a},{b})', bitwise(f, x, y, Q), 0, False
            sx, sy = (x - Q if x >= Q // 2 else x), (y - Q if y >= Q // 2 else y)
            for cname, cv in (('eq', x == y), ('ltu', x < y), ('lts', sx < sy), ('leu', x <= y), ('les', sx <= sy)):
                yield f'{cname}({a},{b})', int(cv), 0, False
            is_lit = b not in ('0', 'n', 'w')
            s = abs(int(b)) if is_lit else 0
            neg = is_lit and int(b) < 0
            for rule in ('mod', 'sat'):
                for op, z in shift_forms(x, y, w, Q, rule).items():
                    yield f'{op}[{rule}]({a},{b})', z, s, neg


def check_forms():
    lits = [c for c in range(-12, 13) if c != 0]
    c_P = 12
    stats = {}
    for j in (8, 16, 32, 64, 9, 13, 17, 25):
        pow2 = j & (j - 1) == 0
        w = 16 * j
        Q = 1 << w
        m0 = next(m for m in range(c_P + 1, c_P + 1 + 2 * w) if (Q - m) % w == 0)
        for t in (0, 1, 2, 3):
            m = m0 + w * t
            n = Q - m
            assert width(n) == w, (j, m)
            for name, z, s, neg in forms(n, w, Q, lits):
                if z % 2 == 0:
                    continue
                bound = (1 << (s + 1)) * max(m, w, c_P)
                ok = norm(z, Q) <= bound or norm((1 << s) * z, Q) <= bound
                key = ('pow2 j' if pow2 else 'other j', 'negative-literal count' if neg else 'all other forms')
                tot, bad = stats.get(key, (0, 0))
                stats[key] = (tot + 1, bad + (not ok))
    for key in sorted(stats):
        tot, bad = stats[key]
        print(f'(1) {key[0]:7s} {key[1]:22s}: odd forms {tot:6d}, violating q in {{1,2^s}}, '
              f'|delta| <= 2^(s+1)*max(m,w,c_P): {bad}')


def check_bytes():
    w = 14592  # 16*912 > (2/9)*256^2
    Q = 1 << w
    m = next(m for m in range(10, 10 + 4 * w) if (Q - m) % w == 0)
    n = Q - m
    L = n // w
    bad = 0
    tested = 0
    nb = w // 8
    for s in range(1, 9):
        for t in range(1, 1 << s):
            centre = t * (Q >> s)
            top = centre >> (w - 8)
            delta_band = 2 * L + 2 * (1 << s) * 2 * max(m, w)
            # adversarial ASCII words: top byte equal (or one off), next byte at the extremes
            for tb in (top, top - 1, top + 1):
                if not (9 <= tb <= 126):
                    continue
                for nxt in (9, 10, 32, 126):
                    for fill in (9, 126):
                        v = tb << (w - 8) | nxt << (w - 16)
                        for k in range(nb - 2):
                            v |= fill << (8 * k)
                        tested += 1
                        if norm(v - centre, Q) <= delta_band:
                            bad += 1
    print(f'(2) w={w}: adversarial ASCII words tested {tested}, within the band radius of a nonzero '
          f'multiple of Q/2^s (s<=8): {bad}')

def check_regimes():
    lo = hi = 0
    for j in range(20, 400):
        N = 8 * 128 * (j + 1) * 10 ** j
        w = width(N)
        Q = 1 << w
        if N < Q // 2:
            lo += 1
        else:
            hi += 1
    print(f'(3) decimal family N=1024(j+1)10^j, j in [20,400): lower half (N<Q/2): {lo}, upper half: {hi}')

if __name__ == '__main__':
    check_forms()
    check_bytes()
    check_regimes()
