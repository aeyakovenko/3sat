#!/usr/bin/env python3
"""For the-list-distinctness-technique-cannot-certify-more-than-n-log-n.md:
the cell identity behind the characteristic-3 network for
[AB = C] over F_3 (journal: matching-characteristic-networks-for-binary-products.md,
section 'Many factors and any fixed input field'; Lean statement cell_indicator in
upstream-checks/MatchingCharacteristicProduct.lean, which needs Mathlib, not run here).

For one output cell with row a in F_3^d, column b in F_3^d and proposed value c:
  [a.b = c] = 1 - (a.b - c)^2   in F_3,
and expanding, sum over choices  none (weight 1)  or an ordered pair (s1, s2) of
summands from {C} u {1..d} (weight -t_{s1} t_{s2}, t_C = -c, t_h = a_h b_h)
gives the indicator.  Each choice requests at most two entries of A and two of B,
so the whole network has 2d^2 selected lookups, verified by one sort per bank:
O(d^2 log^2 d) volume.  Exhaustive over all (a, b, c) for d = 1, 2, 3.
"""
import itertools

def cell_sum(a, b, c, d):
    terms = [(-c) % 3] + [(a[h] * b[h]) % 3 for h in range(d)]
    tot = 1  # 'none' choice
    for s1 in range(d + 1):
        for s2 in range(d + 1):
            tot -= terms[s1] * terms[s2]
    return tot % 3

if __name__ == '__main__':
    for d in (1, 2, 3):
        bad = 0; n = 0
        for a in itertools.product(range(3), repeat=d):
            for b in itertools.product(range(3), repeat=d):
                ab = sum(x * y for x, y in zip(a, b)) % 3
                for c in range(3):
                    n += 1
                    if cell_sum(a, b, c, d) != (1 if ab == c else 0):
                        bad += 1
        print(f"d={d}: cells checked={n} mismatches={bad} choices per cell={1+(d+1)**2}")
