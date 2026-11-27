"""Exponent bookkeeping for description-first games against the hard-table opponent.
Run: python3 description_first_exponent_table.py   (needs sympy)

Quantities are t^alpha / L^beta; t = number of opponent steps (= trace rows up to a
constant), L = Theta(log t).  Constants are dropped; only exponents are tracked.

Compiler costs (journal):  a nondeterministic RAM run with clock R and p public bits
compiles to CNF of  R*L^a + p*L^c  bits, a = 3 (packed-band-transfer.md),
c = 1 (materialized-input-census.md: m words cost m*L^2, i.e. L per bit).
SAT is solved in time  len^k  (SAT exponent k).  Native setting: a = c = 0.
rho = L^r decoder calls per trace row: r = 0 word lookups, r = 1 bit lookups
(or the predecessor search of an address-sorted store log, log T = Theta(L)).
"""
from fractions import Fraction as F
import sympy as sp

# ---- 1. structural identity, symbolic in a, c, k, r --------------------------------
a, c, k, r, lt, lL = sp.symbols('a c k r logt logL', positive=True)
# hard table: T = (h L^a)^k = t  ->  log h = (log t)/k - a log L
logh = lt / k - a * lL
# defect formula rho*d*L^a + s*L^c must exceed h^(1/k):
d_star = logh / k - (a + r) * lL          # log of decoder-time threshold
s_star = logh / k - c * lL                # log of advice threshold
# two-block driver: l1 = s L^a + b L^c ; l2 = l1^k L^a ; time l2^k = l1^(k^2) L^(a k) = o(t)
logl1 = (lt - a * k * lL) / k**2
s_budget = logl1 - a * lL
b_budget = logl1 - c * lL
print("symbolic check (r = 0):")
print("  d* - s_budget =", sp.simplify((d_star - s_budget).subs(r, 0)))
print("  s* - b_budget =", sp.simplify(s_star - b_budget))
print("  d* - s_budget (general r) =", sp.simplify(d_star - s_budget))

# ---- 2. numeric table ---------------------------------------------------------------
def hard_table(k, a, c, r):
    """thresholds as (alpha, beta): advice s*, decoder d*."""
    al = F(1, k * k)
    return (al, F(a, k) + c), (al, F(a, k) + a + r)

def budget_refined(k, a, c, j):
    """j-block driver, refined charge: innermost l1 = s L^a + b L^c, each outer level
    l_{i+1} = l_i^k L^a (+ its own prefix bits, never larger), final time l_j^k = o(t).
    Returns budgets (alpha, beta) for b (first-block bits) and s."""
    # exponent bookkeeping: time = l1^(k^j) * L^(a*(k + k^2 + ... + k^(j-1)) * ... )
    # do it by recursion on (power of l1, power of L)
    p, q = 1, 0                      # l_i = l1^p * L^q
    for _ in range(j - 1):
        p, q = p * k, q * k + a      # l_{i+1} = l_i^k * L^a
    p, q = p * k, q * k              # final SAT call: time = l_j^k
    al = F(1, p)
    beta_l1 = F(q, p)                # l1 = o(t^(1/p) / L^(q/p))
    return (al, beta_l1 + c), (al, beta_l1 + a)

def budget_crude(k, a, j):
    """note's charge: (n+s+b) L^a per level, same for b and s."""
    (_, _), (al, be) = budget_refined(k, a, a, j)
    return (al, be)

def fmt(x):
    al, be = x
    return f"t^{al} / L^{be}"

def verdict(lower, budget):
    """lower bound >= c*lower vs requirement o(budget): excluded iff lower >~ budget."""
    (al1, be1), (al2, be2) = lower, budget
    if al1 != al2:
        return "excluded (poly margin)" if al1 > al2 else "NOT excluded (poly window)"
    if be1 <= be2:
        return "excluded" + ("" if be1 == be2 else f" (margin L^{be2 - be1})")
    return f"NOT excluded (window L^{be1 - be2})"

print("\nA. hard-table thresholds and the M-notation c0 (M = t*L table bits)")
print(f"{'setting':10s} {'advice s*':18s} {'word d*':18s} {'bit d*':18s} "
      f"c0(s)  c0(q,word)  c0(q,bit)  c0(circuit, tight note)")
for name, kk, aa, cc in [("native k=1", 1, 0, 0), ("SAT k=1", 1, 3, 1),
                         ("SAT k=2", 2, 3, 1), ("SAT k=3", 3, 3, 1)]:
    s_, dw = hard_table(kk, aa, cc, 0)
    _, db = hard_table(kk, aa, cc, 1)
    c0 = lambda x: x[1] + x[0]          # t^al/L^be = M^al / m^(be+al)
    circ = (F(1, kk * kk), F(aa, kk) + 2)
    print(f"{name:10s} {fmt(s_):18s} {fmt(dw):18s} {fmt(db):18s} "
          f"{str(c0(s_)):6s} {str(c0(dw)):11s} {str(c0(db)):10s} "
          f"{str(c0(circ)) if aa else '-'}")

print("\nB. two-block description games (b >= E, s >= rho_path*d) against the budgets")
for name, kk, aa, cc in [("native k=1", 1, 0, 0), ("SAT k=1", 1, 3, 1),
                         ("SAT k=2*", 2, 3, 1), ("SAT k=3*", 3, 3, 1)]:
    s_, dw = hard_table(kk, aa, cc, 0)
    _, db = hard_table(kk, aa, cc, 1)
    bb, sb = budget_refined(kk, aa, cc, 2)
    cr = budget_crude(kk, aa, 2)
    print(f"{name}: refined budget b = o({fmt(bb)}), s = o({fmt(sb)}); crude s+b = o({fmt(cr)})")
    print(f"   advice  E vs b-budget        : {verdict(s_, bb)}")
    print(f"   word d  vs s-budget          : {verdict(dw, sb)}")
    print(f"   bit d, path pays one bit     : {verdict(db, sb)}")
    print(f"   bit d, path pays a full word : {verdict(db, (sb[0], sb[1] + 1))}")  # path pays L*d per word
    print(f"   min(E*,d*) vs crude s+b      : {verdict(max(s_, dw, key=lambda x: x[1]), cr)}")

print("\nC. linear SAT (k=1), j blocks; description = first block; word decoders")
s_, dw = hard_table(1, 3, 1, 0)
for j in range(1, 6):
    if j == 1:
        # no switch: b = 0; the description is guessed on the path at w = L bits/step
        sb = budget_refined(1, 3, 1, 1)[1]
        low = max([(s_[0], s_[1] + 1), dw], key=lambda x: x[1])  # s >= min(E/L, d)
        print(f"  j=1: s-budget o({fmt(sb)}); path >= min(E/L, d) >= {fmt(low)}: {verdict(low, sb)}")
        continue
    bb, sb = budget_refined(1, 3, 1, j)
    cr = budget_crude(1, 3, j)
    print(f"  j={j}: b o({fmt(bb)}) -> {verdict(s_, bb)};  s o({fmt(sb)}) -> {verdict(dw, sb)};"
          f"  crude s+b o({fmt(cr)}) -> {verdict(dw, cr)}")

print("\nD. native j-block criterion (k=1): budget o(t) for fixed j, O(t/log^eps t) for j=o(loglog t)")
print(f"  hard table (word): E + d >= {fmt(hard_table(1, 0, 0, 0)[1])}  -> excluded for every fixed j >= 2 and every eps > 0")
