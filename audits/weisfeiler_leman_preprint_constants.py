"""Derived thresholds for the parameter choices of the Weisfeiler-Leman time-bound preprint (derived for the
journal note weisfeiler-leman-time-bound-and-the-compiler-route.md; not stated in the paper).

Paper (Section 6, eq. (6.1)): s = floor(r/1000), p = floor(s/1000), c0 = 1e-9, K = r + 1,
r = k (joint convention) or r = k - 1 (separate convention).
Conditions used in the proof:
  Lemma 6.1:  d = floor(r/3),  20 s <= r/50 < d,  20 s < r - d
  (6.6):      D + 50 p < s,    20 c0 k < p
The paper calls D "an absolute constant"; its proof of Lemma 6.2 displays the one-tape exponent
760 + 12 p. D = 760 is one value the displayed bound supports (D >= 722 suffices for all p >= 1);
the least k is 10**6 for every D <= 949. Both facts are computed below.

Usage: python3 -I -B weisfeiler_leman_preprint_constants.py   (no arguments; under a second)
"""
import sys
from fractions import Fraction

sys.dont_write_bytecode = True

C0 = Fraction(1, 10**9)
D = 760


def conditions(k: int, convention: str, dval: int = D) -> bool:
    r = k if convention == "joint" else k - 1
    s = r // 1000
    p = s // 1000
    d = r // 3
    lemma61 = (20 * s <= Fraction(r, 50) < d) and (20 * s < r - d)
    gaps = (dval + 50 * p < s) and (20 * C0 * k < p)
    return lemma61 and gaps and r >= 3


def least_k(convention: str, dval: int = D) -> int:
    # p >= 1 is forced by 20*c0*k < p with k > 0, i.e. s >= 1000, r >= 10**6.
    k = 10**6 - 10
    while not conditions(k, convention, dval):
        k += 1
    return k


def main() -> None:
    for conv in ("joint", "separate"):
        k = least_k(conv)
        r = k if conv == "joint" else k - 1
        s, p = r // 1000, (r // 1000) // 1000
        print(f"{conv:8s}: least k meeting the displayed conditions with D={D}: k={k} "
              f"(r={r}, s={s}, p={p}, d={r // 3}); lower-bound exponent c0*k = {float(C0 * k):.6f}")
    # Smallest D with 760 + 12p <= D + 50p for every p >= 1 (the displayed bound fits m^(D+50p)):
    d_min = max(760 + 12 * p - 50 * p for p in range(1, 10**4))
    print(f"smallest D with 760+12p <= D+50p for all p>=1: D={d_min}")
    # Largest D for which the least joint k stays 10**6 (scan D upward until it changes):
    dval = d_min
    while least_k("joint", dval + 1) == 10**6:
        dval += 1
    print(f"least joint k is 10**6 for every D in [{d_min}, {dval}]; at D={dval + 1} it is {least_k('joint', dval + 1)}")
    # Number of graph orders tried per word in Lemma 6.2: |I_m| = (m+1)^20 - m^20, compared with 20 m^19.
    for m in (10, 100, 1000):
        size = (m + 1) ** 20 - m ** 20
        print(f"m={m}: |I_m|={size:.6e}, |I_m|/(20 m^19)={size / (20 * m ** 19):.4f}")
    # Where n^(c0 k) first exceeds the explicit input length 2 n^2 (two adjacency matrices):
    k_input = int(2 / C0) + 1
    print(f"n^(c0 k) > n^2 (input-reading scale) needs c0*k > 2, i.e. k >= {k_input}")
    # Compression actually used by the transfer: source run of M_s has time C*m^(20 s) (Thm 5.2),
    # output graph order n in [m^20, (m+1)^20), i.e. about m^40 adjacency bits.
    for k in (10**6, 10**7, 2 * 10**9 + 1):
        r = k
        s = r // 1000
        print(f"k={k}: source time exponent 20s={20 * s}, output-bit exponent 40, "
              f"ratio 40/(20s)={40 / (20 * s):.3e}; Thm 4.3 unpadded order m^6 -> bits m^12, "
              f"budget exponent d=floor(r/3)={r // 3}")


if __name__ == "__main__":
    main()
