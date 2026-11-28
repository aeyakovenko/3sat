# Two-cursor linear-time decider for the constant-palette equality files of
# notes/communication-bound-for-public-crossed-scans.md.  17 stored instructions.
# Phase A: S = first word whose low 16 bits are two spaces (Alice's first literal word).
A1:   x = load r
      t = and x 65535
      br eq t 8224 B0 A2
A2:   r = add r 1 -> A1
# P = all-space word, from the sign word x = [sp]*(W-2)+[sign,'1'].
B0:   h = shl x 16
      v = or h 8224
# Hare q = S + 2j until M[q] = P (first padding word E); then j = H = half the body.
B1:   j = add j 1
      q = add j j
      q = add q r
      x = load q
      br eq x v C1 B1
# Compare M[r] with M[r+H]; the first mismatch is either real (NO) or r = S+H, where M[r+H] = P (YES).
C1:   x = load r
      s = add r j
      z = load s
      br ne x z C3 C2
C2:   r = add r 1 -> C1
C3:   br eq z v YES NO
