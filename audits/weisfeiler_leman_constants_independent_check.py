"""Independent check, written during review from the preprint's conditions and not copied from
weisfeiler_leman_preprint_constants.py, of the derived numbers in the journal note
weisfeiler-leman-time-bound-and-the-compiler-route.md.
Usage: python3 -I -B weisfeiler_leman_constants_independent_check.py   (no arguments)

Conditions (from the preprint's TeX, Section 6):
  Lemma 6.1 proof:  d = floor(r/3), 20 s <= r/50 < d, 20 s < r - d
  (6.6):            D + 50 p < s,  20 c0 k < p
  s = floor(r/1000), p = floor(s/1000), c0 = 1e-9, r = k (joint) or k - 1 (separate).
"""
import sys
from fractions import Fraction

sys.dont_write_bytecode = True
C0 = Fraction(1, 10**9)


def ok(k, conv, D):
    r = k if conv == "joint" else k - 1
    s, d = r // 1000, r // 3
    p = s // 1000
    return (r >= 3 and 20 * s <= Fraction(r, 50) < d and 20 * s < r - d
            and D + 50 * p < s and 20 * C0 * k < p)


def least(conv, D, lo=1):
    # brute force from 1 would be slow; but p>=1 needs r>=10**6, so scan a window and
    # separately confirm that no k below the window can satisfy 20 c0 k < p.
    for k in range(lo, 10**6 + 100):
        r = k if conv == "joint" else k - 1
        if (r // 1000) // 1000 >= 1:
            break
    else:
        raise SystemExit("unexpected")
    first_p1 = k  # first k with p >= 1
    k = first_p1
    while not ok(k, conv, D):
        k += 1
    return first_p1, k


for D in (0, 722, 760, 949, 950):
    for conv in ("joint", "separate"):
        first_p1, k = least(conv, D, lo=10**6 - 50)
        print(f"D={D:4d} {conv:8s}: first k with p>=1: {first_p1}; least k meeting all displayed conditions: {k}")

# all k in a window above 10**6 satisfy the conditions (D=760), plus sampled larger k
bad = [k for k in range(10**6, 10**6 + 200001) if not ok(k, "joint", 760)]
print("joint, D=760, k in [1e6, 1e6+2e5]: failures =", len(bad))
samples = [10**7, 123456789, 2 * 10**9, 2 * 10**9 + 1, 10**12 + 7]
print("sampled larger k all ok:", all(ok(k, "joint", 760) and ok(k + 1, "separate", 760) for k in samples))

# smallest absolute D with 760 + 12 p <= D + 50 p for every p >= 1
print("smallest D with 760+12p <= D+50p for all p>=1:", max(760 - 38 * p for p in range(1, 1000)))

# c0 k > 2 threshold
k2 = next(k for k in range(2 * 10**9 - 3, 2 * 10**9 + 5) if C0 * k > 2)
print("least k with c0*k > 2:", k2)

# number of orders tried per word length m: |I_m| = (m+1)^20 - m^20 ~ 20 m^19
for m in (10, 100, 1000):
    size = (m + 1) ** 20 - m ** 20
    print(f"m={m}: |I_m| = {size:.6e}, |I_m|/m^19 = {size / m**19:.4f}")
