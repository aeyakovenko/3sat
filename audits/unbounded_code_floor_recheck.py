# Recompute the counting floors of Theorem 2 in the-ceiling-of-the-unbounded-code-clock.md
# (closed form and exact bit-length evaluation), and the ceiling W(w+1), for the table rows.
# An independent reimplementation (not unbounded_code_ceiling_audit.py), written for
# what-any-proof-of-superlinear-sat-time-must-get-past.md.
import math
rows = [(4,4),(4,5),(8,4),(16,16),(64,16)]   # (W words, w bits)
for W,w in rows:
    N = W*w
    rhs = N - 1 - math.log2(6 + 2*math.log2(2*N + 2**w))
    closed_T = math.floor(rhs)            # T = integer part of RHS: fraction <= 2^-2^(T+1) have clock <= T
    # exact: largest T with (26 q^2)^(2^(T+1)-1) < 2^(2^N - 1), log2 bounded by integer bit length
    best = -1
    for T in range(0, N+1):
        q = T + 2**w
        lhs_bits = (2**(T+1) - 1) * (26*q*q).bit_length()
        if lhs_bits < 2**N - 1:
            best = T
    print(f"W={W:2d} w={w:2d} N={N:5d}  ceiling W(w+1)={W*(w+1):5d}  closed-form floor(RHS)={closed_T:5d}  "
          f"exact: more than half need >= {best+1:5d}")
