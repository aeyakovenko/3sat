#!/usr/bin/env python3
"""Build real equality files with the journal's generator equality_file_generator.py, for
notes/even-multiplier-scans-with-odd-strides-fail-at-every-speed.md, and
  (1) `static`: check the covered-swap hypotheses (H2) and (H3) on files at the standard width (the cover
      count accepts any unchanged odd cell, see covers(); the Theorem uses u- and v-sign covers only)
      w = 16*ceil(D*log2(N+2)/16), N = 2^17..2^22, D = 1, 2, 3, plus non-power-of-two lengths;
  (2) `write DIR`: write w=24 memories (equal file, unequal file with one Bob bit flipped, and the
      uncovered control) for the real mode of even_multiplier_covered_swap_checks.cpp.
Run from audits/: python3 -I -B even_multiplier_equality_file_covers.py [static | write DIR]
(no argument: static, about a second; write DIR writes four files into DIR)"""
import sys, os, math, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from equality_file_generator import build, validate, width

def sign_words(W):
    pos = int.from_bytes((' ' * (W - 2) + ' ' + '1').encode(), 'little')
    neg = int.from_bytes((' ' * (W - 2) + '-' + '1').encode(), 'little')
    return neg, pos

def layout(f):
    """positions of the x_i sign words (4 per group) in Alice's and Bob's halves, from the generator's recipe"""
    W, K, k = f['W'], f['K'], f['k']
    lit_words = K + 1
    clause = 3 * lit_words + 1
    group = 4 * clause
    hw = (f['alpha_word'] + 1) - k * group          # header words
    A = [[hw + (i - 1) * group + j * clause for j in range(4)] for i in range(1, k + 1)]
    B = [[hw + k * group + (i - 1) * group + j * clause for j in range(4)] for i in range(1, k + 1)]
    return hw, group, clause, A, B

def covers(words, c, d, val, swapped, nwords):
    # Accepts any unchanged odd cell as a cover, including other groups' x-sign cells, whose values depend on
    # the strings; the Theorem uses u- and v-sign covers only, which
    # even_multiplier_equality_file_covers_independent_check.py tests.
    """first j>=1 with c+j*d inside the file, odd, not swapped, holding val; None if the scan leaves the file first"""
    j = 1
    while True:
        a = c + j * d
        if a < 0 or a >= nwords:
            return None
        if a % 2 == 1 and a not in swapped and words[a] == val:
            return j
        j += 1

def static():
    rng = random.Random(2026)
    print('N D w W k K hw%2 K%2 | odd-address occurrences uNeg uPos | n in [uPos,uNeg]? | '
          'Bob groups with (H2) for all 4 cells, d=+1 -1 +3 -3 +5 -5 +7 -7 | (H3) good groups a=2,4,6,8,-2,n,w (d=+1)')
    cases = []
    for D, CD in ((1, 32), (2, 56), (3, 80)):
        for e in (17, 18, 19, 20, 21, 22):
            cases.append((2 ** e, D, CD))
    for t in range(6):  # non-power-of-two byte-aligned lengths
        cases.append((8 * rng.randrange(2 ** 15, 2 ** 18), 1, 32))
    allok = True
    smallvals = []
    for N, D, CD in cases:
        f = build(N, D, CD, rng=rng)
        if f is None or f['k'] < 4:
            print(N, D, 'does not fit'); continue
        validate(f)
        words, w, W = f['words'], f['w'], f['W']
        Q = 1 << w
        nwords = len(words)
        uNeg, uPos = sign_words(W)
        assert nwords < uPos, 'file addresses must lie below the sign words'
        img = set(words) | {0}
        small = sorted(v for v in img if v < nwords)
        assert all(v % 2 == 0 for v in small), ('odd file address in the palette', small)
        fullmin = min(words[:-1])
        assert fullmin >> (w - 8) >= 10 and fullmin >= nwords, 'a full word below the file addresses'
        smallvals.append((N, D, small))
        hw, group, clause, A, B = layout(f)
        # check the recipe positions against the actual words
        for g4 in A + B:
            for c in g4:
                assert words[c] in (uNeg, uPos)
        oddNeg = sum(1 for a in range(1, nwords, 2) if words[a] == uNeg)
        oddPos = sum(1 for a in range(1, nwords, 2) if words[a] == uPos)
        nsep = uPos <= N <= uNeg
        res = []
        for d in (1, -1, 3, -3, 5, -5, 7, -7):
            good = 0
            for g4 in B:
                sw = set(g4)
                ok = True
                for c in g4:
                    if covers(words, c, d, uNeg, sw, nwords) is None or covers(words, c, d, uPos, sw, nwords) is None:
                        ok = False; break
                good += ok
            res.append(good)
        h3 = []
        for a in (2, 4, 6, 8, -2, N, w):
            good = 0
            for g4 in B:
                ok = True
                for c in g4:
                    for z in [(a * (c + j)) % Q for j in (-1, 0, 1)] + [c, c + 1]:
                        if uPos <= z <= uNeg:
                            ok = False
                good += ok
            h3.append(good)
        print(N, D, w, W, f['k'], f['K'], hw % 2, f['K'] % 2, '|', oddNeg, oddPos, '|', nsep, '|',
              ' '.join(str(x) for x in res), '/', f['k'], '|', ' '.join(str(x) for x in h3))
        if min(res[:2]) < f['k'] - 1 or oddNeg == 0 or oddPos == 0:
            allok = False
    print('static: palette values that are file addresses (all even; asserted no odd one):', sorted(set(tuple(x[2]) for x in smallvals)))
    print('static: every file has odd-address occurrences of both sign words and (H2) for d=+-1 in all but at most one Bob group:', allok)
    # the exceptional lengths: n between the two sign words, D=1
    for w in (32, 48, 64):
        W = w // 8
        uNeg, uPos = sign_words(W)
        print('exceptional n-interval at w=%d: [%d, %d], length %d = 13*2^(w-16)+1, log2(uPos)=%.4f' %
              (w, uPos, uNeg, uNeg - uPos + 1, math.log2(uPos)))

def write(outdir):
    os.makedirs(outdir, exist_ok=True)
    rng = random.Random(77)
    N = 2 ** 20
    f0 = build(N, 1, 32, w=24, rng=rng)
    k = f0['k']
    a = [rng.randrange(2) for _ in range(k)]
    i = k // 2  # Bob's middle group (1-based index i)
    b = list(a); b[i - 1] ^= 1
    feq = build(N, 1, 32, w=24, a_bits=a, b_bits=list(a), rng=rng)
    fne = build(N, 1, 32, w=24, a_bits=a, b_bits=b, rng=rng)
    bc = list(a); bc[k - 1] ^= 1  # control: Bob's last group, uncovered for d=+1
    fct = build(N, 1, 32, w=24, a_bits=a, b_bits=bc, rng=rng)
    for f in (feq, fne, fct):
        validate(f)
    hw, group, clause, A, B = layout(feq)
    cells = B[i - 1]
    ccells = B[k - 1]
    diff = [t for t in range(len(feq['words'])) if feq['words'][t] != fne['words'][t]]
    assert diff == cells, (diff, cells)
    diffc = [t for t in range(len(feq['words'])) if feq['words'][t] != fct['words'][t]]
    assert diffc == ccells
    uNeg, uPos = sign_words(feq['W'])
    import struct
    for name, f in (('equal', feq), ('unequal', fne), ('ctrl_unequal', fct)):
        with open(os.path.join(outdir, name + '.bin'), 'wb') as fh:
            fh.write(struct.pack('<%dI' % len(f['words']), *f['words']))
    with open(os.path.join(outdir, 'meta.txt'), 'w') as fh:
        fh.write('%d %d %d %d %d %d %s %d %s\n' % (feq['w'], len(feq['words']), N, uNeg, uPos, len(cells),
                 ' '.join(map(str, cells)), len(ccells), ' '.join(map(str, ccells))))
    print('wrote', outdir, 'N=%d w=%d k=%d K=%d words=%d alpha=%d flipped Bob bit %d at cells %s; control cells %s; uNeg=%d uPos=%d' %
          (N, feq['w'], k, feq['K'], len(feq['words']), feq['alpha_word'], i, cells, ccells, uNeg, uPos))

if __name__ == '__main__':
    if len(sys.argv) == 1 or sys.argv[1] == 'static':
        static()
    else:
        write(sys.argv[2])
