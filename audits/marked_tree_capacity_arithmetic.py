"""Marked-tree recurrence of EightStepMarkedCapacity.lean, evaluated on capacity lists.
weights[d] = cap on targets at an accepting leaf whose path has d comparisons (d=1..K);
F_d = max(w_d, 2 F_{d+1}), E_d = F_{d+1} + E_{d+1}, F_{K+1}=E_{K+1}=0.
A marked root (one rejecting file must be separated) covers at most E_0 = sum_{d>=1} F_d.
Written for four-instructions-per-sign-plane-pair-at-every-width.md."""
from fractions import Fraction

def bound(ws):            # ws = [w_0, w_1, ..., w_K]; same recursion as the Lean `bound`
    f, e = 0, 0
    for w in reversed(ws):
        f, e = max(w, 2 * f), f + e
    return f, e

cases = {
    "journal k=4 caps (16-bit census)": ([0, 36, 18, 8, 1], 64),
    "journal k=4 caps (20-bit census)": ([0, 18, 18, 8, 1], 64),
    "Kraft pattern 64/2^c, k=4":        ([0, 32, 16, 8, 4], 64),
}
for name, (ws, S) in cases.items():
    f, e = bound(ws)
    print(f"{name}: weights {ws[1:]}  marked-root capacity E_0={e}  targets |S|={S}  closes={e < S}")

# Kraft pattern w_d = |S| 2^-d for general K: E_0 = |S| (1 - 2^-K) < |S| for every K.
for K in (2, 4, 6, 8, 10):
    S = 2 ** (K + 4)
    ws = [0] + [S >> d for d in range(1, K + 1)]
    print(f"Kraft K={K}: |S|={S} E_0={bound(ws)[1]} margin={S - bound(ws)[1]} (= |S| 2^-K = {S >> K})")

# Which single-depth excess breaks the k=4 argument? Raise one cap at a time.
base = [0, 36, 18, 8, 1]
for d in range(1, 5):
    ws = list(base);
    while bound(ws)[1] < 64: ws[d] += 1
    print(f"k=4: cap at depth {d} raised from {base[d]} to {ws[d]} first gives E_0={bound(ws)[1]} >= 64")
