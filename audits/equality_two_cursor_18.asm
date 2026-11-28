# Two-cursor linear-time decider for the constant-palette equality files of
# notes/communication-bound-for-public-crossed-scans.md (Alice's half, then Bob's, then padding).
# Run with five_slot_ram_interpreter.py. 18 stored instructions.
# Phase A: S = first word whose low 16 bits are two spaces (first literal word of Alice's half).
A1:   x = load r
      t = and x 65535
      br eq t 8224 B0 A2
A2:   r = add r 1 -> A1
# Phase B: P = all-space word, built from the sign word x = [sp]*(W-2)+[sign,'1'].
B0:   h = shl x 16
      v = or h 8224
      q = mov r
# hare q and tortoise p from S: when M[q] = P (first padding word E), p = S + (E-S)/2.
      p = mov r
B1:   q = add q 2
      p = add p 1
      x = load q
      br eq x v C1 B1
# Phase C: compare Alice word r with Bob word p until p reaches E = q.
C1:   x = load r
      z = load p
      br ne x z NO C3
C3:   r = add r 1
      p = add p 1
      br eq p q YES C1
