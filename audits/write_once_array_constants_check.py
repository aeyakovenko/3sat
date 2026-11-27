"""Recompute the constants and thresholds of Lemmas A and A' of
notes/mutable-arrays-on-word-write-once-memory.md (written during review).
Run: python3 write_once_array_constants_check.py   (instant)
"""
import math
L2 = math.log2
print("== Lemma A constants (m >= 2^20, w >= 20, r >= 1, ell >= 8(r+2)w >= 480, B >= 8wt_u) ==")
m1 = 1/8; m2 = (16/7)/8; cnt = (5*L2(481)+7)/480; m4 = 2**-10*L2(math.e*2**10); m5 = 20*2**-20
print(f"(M1)+count {m1:.4f}  (M2) cells {m2:.4f}  counts+ceilings {cnt:.4f}  (M4) {m4:.4f}  (M5) {m5:.2e}")
exact = m1+m2+cnt+m4+m5; rounded = 1/8+2/7+0.11+0.012+1e-4
print(f"sum with exact terms {exact:.4f}; sum of the note's rounded bounds {rounded:.4f} (the note uses <= 0.533)")
for R in (exact, rounded, 0.53):
    print(f"  R/ell={R:.4f}: beta >= 2^-R/e - 2^-10 = {2**-R/math.e - 2**-10:.4f}")
print("== Lemma A' constants (ell >= 960, ell' >= 0.49 ell, B >= 120 w tbar') ==")
post = 15*(8/7)/0.49/120; regs = 1/(16*0.49); cnt2 = (3*L2(961)+6)/(0.49*960)
print(f"post {post:.4f} (note <0.30)  regs {regs:.4f} (note 0.13)  counts {cnt2:.4f} (note 0.08)")
ex2 = post+regs+cnt2+m4+m5; rd2 = 0.30+0.13+0.08+0.012+1e-4
print(f"sum exact {ex2:.4f}; sum of rounded bounds {rd2:.4f} (the note uses <= 0.523)")
for R in (ex2, rd2):
    print(f"  R/ell'={R:.4f}: avg beta >= {2**-R/math.e - 2**-10:.4f}")
print("ell' >= 0.49 ell for ell >= 960:", (960//2)/960 >= 0.49, " floor((ell)/2) for odd ell=961:", (961//2)/961)
print("== thresholds ==")
L = 2
while not (L >= 24*L2(8*L+1)): L += 1
print("first log2 m with log2m/(20 log2(8 log2m+1)) - 1/5 >= 1 :", L)
L = 2
while not (3*L <= 2**(L/4)/8): L += 1
print("first log2 m with (r+2)w <= m^(1/4)/8 at r=1, w=log2 m :", L)
L = 2
while not (16*3*L <= 2**(L/4)): L += 1
print("first log2 m with 16(r+2)w <= m^(1/4) at r=1, w=log2 m (Lemma A'):", L)
L=2
while not ((1/25)*(L/(4*L2(120*L*1+1)) - 1) >= 1): L += 1
print("first log2 m where A' consequence bound (t=1, w=log2 m) gives C >= 1:", L)
print("== |T| >= n/5: even positions in (n/2, n] ==")
for n in (3072, 3073, 3074, 3075, 4000):
    cnt = sum(1 for p in range(n//2+1, n+1) if p % 2 == 0)
    print(n, cnt, cnt >= n/5)
print("== count-field width in Lemma A: t_u*Lambda_{j-1} <= sqrt(m)/(7w) < 2^w ==")
