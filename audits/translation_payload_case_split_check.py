#!/usr/bin/env python3
# translation_payload_case_split_check.py -- check, written during review, of the translation-payload remark of
# notes/odd-multiplier-stores-in-a-six-slot-scan.md (index level).
# Writes nothing.  Usage: python3 -B translation_payload_case_split_check.py
# The remark (index level): payload f(z) = z + e on the coset C of the scan p0 + i d mod 2^w
def maxrun_translation(t, L):
    # g(x) = x + t mod L; exact max ascent run (walk)
    best = 0
    for x0 in range(L):
        x, r = x0, 0
        while (x + t) % L > x:
            x = (x + t) % L; r += 1
        best = max(best, r)
    return best
cases = bad = lookahead = leaves = small = 0
for w in range(3, 11):
    Q = 2 ** w
    for d in [1, -1, 2, -2, 3, -3, 4, 5, 6, -6, 12]:
        v = ((d % Q) & -(d % Q)).bit_length() - 1
        L = Q >> v; dp = d >> v if d > 0 else -((-d) >> v)  # odd part, signed
        for e in range(-24, 25):
            cases += 1
            if e % (2 ** v) != 0:
                leaves += 1; continue  # f leaves C (Lemma 0 split, checked elsewhere)
            ep = e // (2 ** v)
            # index offset t in [0, L): t*dp = ep mod L  (dp odd, invertible mod L)
            t = (ep * pow(dp % L, -1, L)) % L if L > 1 else 0
            if t * abs(dp) < L - abs(ep):
                if t * dp != ep: bad += 1; print("case1 fail", w, d, e, t)
                else: lookahead += 1
            elif L >= 2 * abs(ep):
                R = maxrun_translation(t, L)
                if R > 2 * abs(dp) or R > (L - 1) // max(t, 1): bad += 1; print("case2 fail", w, d, e, t, R)
                else: small += 1
print("translation remark: cases=%d leaves-C=%d lookahead(e=t*d,t>=0)=%d R<=2|d'|=%d failures=%d" % (cases, leaves, lookahead, small, bad))
