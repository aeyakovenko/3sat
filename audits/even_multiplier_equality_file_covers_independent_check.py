#!/usr/bin/env python3
"""Independent check, written during review, of Lemma C and the cover claims of
notes/even-multiplier-scans-with-odd-strides-fail-at-every-speed.md (independent of even_multiplier_equality_file_covers.py).
Uses the journal generator equality_file_generator.py. Sign cells are located by scanning the words
(every word equal to uNeg/uPos), not by the recipe; their clause role (x/u/v) is derived from
the position of the preceding end-of-clause word.  Covers are restricted to u- and v-sign
cells (string-independent), as the Theorem uses them.
Usage: python3 -I -B even_multiplier_equality_file_covers_independent_check.py   (no arguments; about a minute)
Writes nothing."""
import sys, os, math, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from equality_file_generator import build, validate, width

def sw(W):
    pos = int.from_bytes((' ' * (W - 1) + '1').encode(), 'little')
    neg = int.from_bytes((' ' * (W - 2) + '-1').encode(), 'little')
    return neg, pos

def analyse(f, ds):
    words, w, W, k, K = f['words'], f['w'], f['W'], f['k'], f['K']
    nwords = len(words)
    uNeg, uPos = sw(W)
    endw = int.from_bytes((' 0\n' + ' ' * (W - 3)).encode(), 'little')
    assert nwords < uPos
    # palette values that are file addresses
    img = set(words) | {0}
    small = sorted(v for v in img if v < nwords)
    assert all(v % 2 == 0 for v in small), small
    # locate clauses: header ends where the first sign word is
    signpos = [t for t in range(nwords) if words[t] in (uNeg, uPos)]
    hw = signpos[0]
    clen = 3 * (K + 1) + 1
    nclauses = 8 * k
    assert len(signpos) == 3 * nclauses, (len(signpos), nclauses)
    role = {}
    for m in range(nclauses):
        s = hw + m * clen
        assert words[s + clen - 1] == endw
        for r, off in (('x', 0), ('u', K + 1), ('v', 2 * K + 2)):
            assert words[s + off] in (uNeg, uPos)
            role[s + off] = (r, m // 4)  # group index 0..2k-1 (Alice 0..k-1, Bob k..2k-1)
    assert set(role) == set(signpos)
    # Lemma C(i): every group has odd u/v occurrences of both words
    ok_i = True
    for gi in range(2 * k):
        vals = set(words[t] for t, (r, g) in role.items() if g == gi and r in 'uv' and t % 2 == 1)
        if vals != {uNeg, uPos}:
            ok_i = False
    uv_odd = {t for t, (r, g) in role.items() if r in 'uv' and t % 2 == 1}
    # covers for Bob's groups, u/v cells only, first lap inside the file
    res = {}
    for d in ds:
        good = 0
        for gi in range(k, 2 * k):
            cells = [t for t, (r, g) in role.items() if g == gi and r == 'x']
            assert len(cells) == 4
            okg = True
            for c in cells:
                need = {uNeg, uPos}
                a = c + d
                while 0 <= a < nwords and need:
                    if a in uv_odd and words[a] in need:
                        need.discard(words[a])
                    a += d
                if need:
                    okg = False; break
            good += okg
        res[d] = good
    return dict(nwords=nwords, hw=hw, ok_i=ok_i, res=res, small=small, k=k, K=K, w=w)

def main():
    rng = random.Random(4242)
    ds = (1, -1, 3, -3, 5, -5, 7, -7, 9, -9, 11, -11, 13, -13, 15, -15)
    cases = []
    for D, CD in ((1, 32), (2, 56), (3, 80)):
        for e in range(17, 24):
            cases.append((2 ** e, D, CD, None))
    for CD in (16, 24, 40, 48):
        for e in (18, 20, 22):
            cases.append((2 ** e, 1, CD, None))
    for t in range(25):
        cases.append((8 * rng.randrange(2 ** 14, 2 ** 19), 1 + (t % 3), (32, 56, 80)[t % 3], None))
    for wf in (24, 40, 64):
        for e in (18, 20):
            cases.append((2 ** e, 1, 32, wf))
    nbad_i = nbad_pred = nfiles = 0
    combos = set()
    gcdfail_rows = []
    for N, D, CD, wf in cases:
        kw = {} if wf is None else {'w': wf}
        # adversarial strings: all zeros, all ones, random
        for mode in ('zeros', 'ones', 'rand'):
            f0 = build(N, D, CD, rng=rng, **kw)
            if f0 is None or f0['k'] < 16:
                continue
            k = f0['k']
            a = [0] * k if mode == 'zeros' else [1] * k if mode == 'ones' else [rng.randrange(2) for _ in range(k)]
            f = build(N, D, CD, a_bits=a, b_bits=list(a), rng=rng, **kw)
            validate(f)
            r = analyse(f, ds)
            nfiles += 1
            combos.add((r['w'], r['hw'] % 2, r['K'] % 2))
            if not r['ok_i']:
                nbad_i += 1
                print('LEMMA C(i) FAILS', N, D, CD, wf, mode)
            for d in ds:
                g = math.gcd(3 * r['K'] + 4, abs(d))
                if g == 1:
                    pred = (k - abs(d)) if d > 0 else k
                    if r['res'][d] < pred:
                        nbad_pred += 1
                        print('COVER PREDICTION FAILS', N, D, CD, wf, mode, 'd', d, r['res'][d], '<', pred)
                else:
                    gcdfail_rows.append((N, D, CD, wf, mode, d, r['K'], r['res'][d]))
            if mode == 'zeros':
                print(N, D, CD, wf, 'w=%d k=%d K=%d hw%%2=%d K%%2=%d' % (r['w'], k, r['K'], r['hw'] % 2, r['K'] % 2),
                      'palette<nwords', r['small'], 'uv-covers', ' '.join('%+d:%d' % (d, r['res'][d]) for d in ds))
    print('files analysed=%d, (w, hw parity, K parity) combinations=%s' % (nfiles, sorted(combos)))
    print('Lemma C(i) failures=%d; first-lap u/v-cover prediction failures (gcd=1)=%d' % (nbad_i, nbad_pred))
    print('gcd(3K+4,|d|)>1 rows (u/v-only covered groups; note predicts 0):', len(gcdfail_rows),
          'max covered=', max((x[-1] for x in gcdfail_rows), default=None))

if __name__ == '__main__':
    main()
