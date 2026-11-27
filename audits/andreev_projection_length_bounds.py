"""Exact and bounded serialized length of the Andreev -> proper ASCII 3-SAT projection
(andreev_dimacs_projection_audit.py), for depth-two-threshold-circuit-bounds-for-3-sat.md.

Canonical parameters (journal note): n = 2^r table bits, m = floor(n/r) bits per row,
h = largest power of two <= r/8 (r >= 8).  Source length n_src = n + r*m.

1. Closed forms for V (header variables) and C (header clauses), checked against encode().
2. Exact byte length L_r (streamed; the layout does not depend on the source bits),
   checked against len(encode(...)) where encode is feasible.
3. A per-line upper bound U(r) on L_r, valid for every r (each fresh id has <= d(V) digits,
   every mask name / anchor has exactly h+1 digits, every hole name <= h+1 digits).
Physical length N_r = 8 * L_r bits.
"""

import os
import sys
from math import log10

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from andreev_projection_copy_audit import encode  # verbatim journal encoder  # noqa: E402


def d(x):
    return len(str(x))


def canonical(r):
    n = 1 << r
    m = n // r
    h = 1
    while 2 * h <= r / 8:
        h *= 2
    return n, m, h


def closed_VC(r, m, h):
    n = 1 << r
    c = -(-m // h)                         # chunks per row
    L = 3 * 10**h - 1                      # reserved mask-name range
    F = r * (2 * c - 1) + 2 * h + 2 * n // h + 1     # fresh ids
    C = L + (h - 1) * 2**h + r * (6 * c - 4) + 6 * n // h + 6 * h - 1
    return L + F, C


def stream_length(r, m, h):
    """Exact byte length, mirroring encode() clause by clause without building the file."""
    n = 1 << r
    L = 3 * 10**h - 1
    V, C = closed_VC(r, m, h)
    total = len(f'p cnf {V} {C}\n')
    nxt = L                                 # last allocated id
    a0, a1, a2 = L + 1, L + 2, L + 3
    nxt = L + 3
    A = h + 1                               # digits of every mask name and anchor
    line = lambda *lits: sum(len(str(t)) for t in lits) + 5   # noqa: E731
    # 7 anchor clauses
    for bits in range(1, 8):
        total += line(*[-a if (bits >> (2 - i)) & 1 else a for i, a in enumerate((a0, a1, a2))])
    # bank-1 units (+2 anchors): sign depends on parity, length: A (+1 if negative) + 2A + 5
    for mask in range(1 << h):
        neg = 0 if bin(mask).count('1') % 2 else 1
        total += A + neg + d(a0) + d(a1) + 5
    # holes: (-a0, name, a1) for name in [1, L] minus the 2*2^h mask names
    mask_names = {int(str(b) + format(mu, f'0{h}b')) for b in (1, 2) for mu in range(1 << h)}
    hole_digits = sum(d(x) for x in range(1, L + 1)) - sum(d(x) for x in mask_names)
    total += (L - len(mask_names)) * (d(a0) + 1 + d(a1) + 5) + hole_digits
    # rows
    address = []
    c = -(-m // h)
    for j in range(r):
        chunks = []
        for _ in range(c):
            nxt += 1
            chunks.append(nxt)
            total += (d(nxt) + 1 + A + d(a0) + 5) + (d(nxt) + A + 1 + d(a0) + 5)
        parity = chunks[0]
        for ch in chunks[1:]:
            nxt += 1
            g = nxt
            total += 4 * (d(parity) + d(ch) + d(g)) + 6 + 20
            parity = g
        address.append(parity)
    nxt += 1
    root = nxt
    total += d(root) + d(a0) + d(a1) + 5
    levels = [root]
    low = h.bit_length() - 1
    for sel in reversed(address[:low]):
        children = []
        for parent in levels:
            for neg in (1, 0):            # literal -sel then sel
                nxt += 1
                ch = nxt
                lit = d(sel) + neg
                total += (d(ch) + 1 + d(parent) + d(a0) + 5) + (d(ch) + 1 + lit + d(a0) + 5) \
                    + (d(ch) + d(parent) + 1 + d(sel) + (1 - neg) + 5)
                children.append(ch)
        levels = children
    for mask in range(1 << h):
        for off, chosen in enumerate(levels):
            total += d(chosen) + 1 + A + (0 if mask & (1 << off) else 1) + d(a0) + 5
    table = []
    for _ in range(n // h):
        nxt += 1
        table.append(nxt)
        total += (d(nxt) + 1 + A + d(a0) + 5) + (d(nxt) + A + 1 + d(a0) + 5)
    for sel in address[low:]:
        red = []
        for lo, hi in zip(table[::2], table[1::2]):
            nxt += 1
            g = nxt
            total += 4 * d(sel) + 2 * d(lo) + 2 * d(hi) + 4 * d(g) + 6 + 20
            red.append(g)
        table = red
    total += d(table[0]) + d(a0) + d(a1) + 5
    assert nxt == V, (nxt, V)
    return total


def upper_bound(r, m, h):
    n = 1 << r
    c = -(-m // h)
    L = 3 * 10**h - 1
    V, C = closed_VC(r, m, h)
    D, A = d(V), h + 1
    U = d(V) + d(C) + 8
    U += 7 * (3 * (A + 1) + 5)
    U += 2**h * ((A + 1) + 2 * A + 5)
    U += (L - 2**(h + 1)) * ((A + 1) + 2 * A + 5)
    U += 2 * (r * c + n // h) * ((D + 1) + (A + 1) + A + 5)
    U += 4 * (r * (c - 1) + n // h - 1) * (3 * (D + 1) + 5)
    U += 2 * (D + 2 * A + 5)
    U += (2 * h - 2) * (2 * (2 * (D + 1) + A + 5) + 3 * (D + 1) + 5)
    U += h * 2**h * ((D + 1) + (A + 1) + A + 5)
    return U


def main():
    # 1 + 2: closed forms and streamed length against the real encoder on a grid
    grid = [(2, 2, 2), (3, 2, 2), (3, 5, 2), (4, 3, 4), (4, 4, 2), (4, 4, 4), (5, 6, 2),
            (5, 6, 4), (6, 10, 1), (6, 10, 4), (7, 18, 2), (8, 32, 1), (8, 32, 2), (9, 56, 1),
            (10, 102, 1), (10, 100, 4), (12, 341, 1), (13, 630, 1), (14, 1170, 1), (16, 4096, 2)]
    for r, m, h in grid:
        f = encode(r, m, h, [0] * ((1 << r) + r * m))
        hdr = f[:f.index(b'\n')].split()
        V, C = closed_VC(r, m, h)
        assert (int(hdr[2]), int(hdr[3])) == (V, C), (r, m, h, hdr, V, C)
        S = stream_length(r, m, h)
        U = upper_bound(r, m, h)
        assert S == len(f) <= U, (r, m, h, S, len(f), U)
    print(f'closed-form V, C and streamed byte length == encode() on {len(grid)} layouts; U >= length')
    # 3: canonical table, exact for r = 8..20
    print('r  h  n_src        L_r(bytes)    N_r(bits)/n_src  U_r*8/n_src  C/(n/h)')
    exact = {}
    for r in range(8, 21):
        n, m, h = canonical(r)
        ns = n + r * m
        S = stream_length(r, m, h)
        U = upper_bound(r, m, h)
        assert S <= U
        V, C = closed_VC(r, m, h)
        exact[r] = 8 * S
        print(f'{r:2d} {h:2d} {ns:10d} {S:14d} {8 * S / ns:12.2f} {8 * U / ns:12.2f} {C / (n / h):8.3f}')
    # bound for all r up to 4096 via U; ratios needed for the lower-bound transfer
    kappa = max(max(exact[r] / (canonical(r)[0] + r * canonical(r)[1]) for r in exact),
                max(8 * upper_bound(*((r,) + canonical(r)[1:])) /
                    (canonical(r)[0] + r * canonical(r)[1]) for r in range(21, 4097)))
    print(f'kappa = sup_(8<=r<=4096) N_r/n_src  <= {kappa:.2f}  (exact for r<=20, U beyond)')
    # padding ratio: N_{r+1} / n_src(r)
    def Nbound(r):
        return exact[r] if r in exact else 8 * upper_bound(*((r,) + canonical(r)[1:]))
    kp = max(Nbound(r + 1) / (canonical(r)[0] + r * canonical(r)[1]) for r in range(8, 4096))
    print(f"kappa' = sup_(8<=r<4096) N_(r+1)/n_src(r) <= {kp:.2f}")
    tail = [8 * upper_bound(*((r,) + canonical(r)[1:])) / (canonical(r)[0] + r * canonical(r)[1])
            for r in range(2048, 4097)]
    print(f'U-ratio over r in [2048,4096]: min {min(tail):.2f}, max {max(tail):.2f}')
    lo, hi = 112 * 8 * log10(2) + 32, 112 * 16 * log10(2) + 32
    print(f'asymptotic leading-term envelope 112*D/h + 32 with D/h in [8 log10 2, 16 log10 2): '
          f'[{lo:.2f}, {hi:.2f})')
    # selected ratios C/(n/h) for large r (leading term 12)
    for r in (64, 256, 1024, 4096):
        n, m, h = canonical(r)
        print(f'r={r}: C/(n/h) = {closed_VC(r, m, h)[1] * 10**6 // (n // h) / 10**6:.6f}')


if __name__ == '__main__':
    main()
