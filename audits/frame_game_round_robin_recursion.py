#!/usr/bin/env python3
"""The Challenger recursion for the frame game on round-robin ladders (notes/frame-value-on-round-robin-ladders.md).

g(L) is the guarantee of the focus Challenger on a focus of L layers (frame DAG of a ladder
segment that is round robin on all steps but possibly its top step), taken over every
Pebbler choice of the minimal blocking set B allowed by Lemma 5 of the frame-game upper-bound note:

  case 1 (lowest layer a <= L - C): |B| = C, spread d <= C, b = a + d - 1;
          Challenger takes the better of stay (L - b layers) and jump (a - 1 layers);
  case 2 (lowest layer a > L - C):  |B| >= max(1, L - a); Challenger jumps (a - 1 layers).

  g(0) = g(1) = 0,
  g(L) = min( min_{a <= L-C, 1 <= d <= C} C + max(g(L-a-d+1), g(a-1)),
              min_{max(1,L-C+1) <= a <= L} max(1, L-a) + g(a-1) ).

Run from audits/: python3 frame_game_round_robin_recursion.py [MODE ...]   (default falsify; nothing is written)
Modes:
  falsify            compare g(T) with every exact frame value recorded in the journal (the frame-game upper-bound
                     note, Section 2, and the lower-bound note, Section 5)
  fastcheck Cmax Lmax  check that the fast recursion equals the brute-force one
  closed Cmax Lmax   check g(L) >= G(L) = C*log2((L+C)/(4C)) and g(L) <= f_C(L) for all C <= Cmax, L <= Lmax
  table C L1,L2,..   print g, G, f_C and C*log2(L/C)
"""
import math
import sys


def grec(C, Lmax):
    g = [0] * (Lmax + 1)
    for L in range(2, Lmax + 1):
        best = None
        # case 1
        for a in range(1, L - C + 1):
            for d in range(1, C + 1):
                b = a + d - 1
                if b > L - 1:
                    break
                val = C + max(g[L - b], g[a - 1])
                if best is None or val < best:
                    best = val
        # case 2
        for a in range(max(1, L - C + 1), L + 1):
            val = max(1, L - a) + g[a - 1]
            if best is None or val < best:
                best = val
        g[L] = best
    return g


def grec_fast(C, Lmax):
    """Same recursion; case 1 uses that g is nondecreasing (asserted), so d = C is the Pebbler's best
    and the best a balances the two sides. Used only for large L; agreement with grec is checked."""
    g = [0] * (Lmax + 1)
    for L in range(2, Lmax + 1):
        best = None
        if L - C >= 1:
            # d = C: options a in [1, L-C]; value C + max(g(L-a-C+1), g(a-1)); minimise over a
            # binary search for the crossing point of the decreasing and increasing sides
            lo, hi = 1, L - C
            while lo < hi:
                mid = (lo + hi) // 2
                if g[L - mid - C + 1] > g[mid - 1]:
                    lo = mid + 1
                else:
                    hi = mid
            for a in (lo - 1, lo, lo + 1):
                if 1 <= a <= L - C:
                    val = C + max(g[L - a - C + 1], g[a - 1])
                    if best is None or val < best:
                        best = val
        for a in range(max(1, L - C + 1), L + 1):
            val = max(1, L - a) + g[a - 1]
            if best is None or val < best:
                best = val
        g[L] = best
        assert g[L] >= g[L - 1], (C, L)
    return g


def fC(C, T):
    # the upper-bound note's Proposition 2: f_C(1) = 0, f_C(L) = min(C, ceil(L/2) + 1) + f_C(ceil(L/2))
    if T <= 1:
        return 0
    h = (T + 1) // 2
    return min(C, h + 1) + fC(C, h)


def G(C, L):
    return C * math.log2((L + C) / (4 * C))


# exact frame values on round-robin ladders, from the frame-game upper-bound note, Section 2 (the journal's exact
# Dymond-Tompa solver), and the lower-bound note, Section 5
EXACT = {}
for T, v in zip(range(2, 13), [2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7]):
    EXACT[(2, T)] = v
for T, v in zip(range(13, 23), [7, 7, 7, 8, 8, 8, 8, 8, 8, 8]):
    EXACT[(2, T)] = v
EXACT[(2, 23)] = 8
EXACT[(2, 24)] = 9
for T, v in zip(range(3, 14), [4, 5, 5, 6, 6, 7, 7, 8, 8, 8, 9]):
    EXACT[(3, T)] = v
EXACT[(3, 14)] = 9
EXACT[(3, 15)] = 9
for T, v in zip(range(4, 12), [5, 6, 7, 7, 7, 8, 9, 9]):
    EXACT[(4, T)] = v
LOWER = {(3, 16): 10, (3, 17): 10, (4, 12): 10}
# the lower-bound note: ladder_rr with M = ceil(T/2) cells, frame values at T = 2..10
for T, v in zip(range(2, 11), [1, 3, 4, 5, 6, 7, 7, 9, 9]):
    EXACT.setdefault(((T + 1) // 2, T), v)
    assert EXACT[((T + 1) // 2, T)] == v, (T, v)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else 'falsify'
    if mode == 'falsify':
        tabs = {}
        bad = 0
        for (C, T), v in sorted(EXACT.items()):
            if C not in tabs:
                tabs[C] = grec(C, 40)
            g = tabs[C][T]
            ok = g <= v
            bad += not ok
            print(f"C={C} T={T}: g_rec={g} exact V={v} f_C={fC(C, T)} G={G(C, T):.2f} {'ok' if ok else 'VIOLATION'}")
        for (C, T), v in sorted(LOWER.items()):
            print(f"C={C} T={T}: g_rec={tabs[C][T]} exact V>={v} (no test)")
        print(f"rows {len(EXACT)} violations {bad}")
    elif mode == 'closed':
        Cmax, Lmax = int(sys.argv[2]), int(sys.argv[3])
        worst = None
        nbad = 0
        for C in range(1, Cmax + 1):
            g = grec(C, Lmax)
            for L in range(1, Lmax + 1):
                if g[L] < G(C, L) - 1e-9:
                    nbad += 1
                    print("CLOSED-FORM VIOLATION", C, L, g[L], G(C, L))
                if C >= 2 and L >= C and g[L] > fC(C, L):
                    nbad += 1
                    print("ABOVE UPPER BOUND", C, L, g[L], fC(C, L))
                if L >= 4 * C:
                    m = g[L] - C * math.log2(L / C)
                    if worst is None or m / C < worst[0]:
                        worst = (m / C, C, L, g[L])
        print(f"C<={Cmax} L<={Lmax}: violations {nbad}; min over L>=4C of (g - C log2(L/C))/C = {worst[0]:.4f} at C={worst[1]} L={worst[2]} g={worst[3]}")
    elif mode == 'fastcheck':
        Cmax, Lmax = int(sys.argv[2]), int(sys.argv[3])
        for C in range(1, Cmax + 1):
            assert grec(C, Lmax) == grec_fast(C, Lmax), C
        print(f"grec == grec_fast for C<={Cmax}, L<={Lmax}")
    elif mode == 'table':
        C = int(sys.argv[2])
        Ls = [int(x) for x in sys.argv[3].split(',')]
        g = grec_fast(C, max(Ls))
        print("C | L | g_rec | G=C*log2((L+C)/4C) | C*log2(L/C) | f_C(L) | g_rec/(C log2(L/C)) | f_C/(C log2(L/C))")
        for L in Ls:
            base = C * math.log2(L / C)
            print(f"{C} | {L} | {g[L]} | {G(C, L):.1f} | {base:.1f} | {fC(C, L)} | {g[L] / base:.4f} | {fC(C, L) / base:.4f}")


if __name__ == '__main__':
    main()
