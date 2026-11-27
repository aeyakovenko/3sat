# 43 stored instructions; see a-43-instruction-sat-program-in-the-five-slot-machine.md.
# Representative-search solver; the candidate pointer j holds the flag address.
# Run with five_slot_ram_interpreter.py (comment lines are not instructions).
# Unpack file bytes to M[-1], M[-2], ... (byte k at address -1-k); e ends at the last byte.
U1:   b = and x 255
      br eq x 0 U6 U3
U3:   e = sub e 1
      store e b
      x = shr x 8 -> U1
U6:   x = load a
      a = add a 1
      br eq x 0 MAIN U1
# One attempt: scan tokens; flag of class rep j lives at j+e (0 unmarked, 2 false, 3 true).
MAIN: q = mov 0
L1:   n = eq c 45
      q = sub q 1
      c = load q
      br ltu c 48 L5 T1
L5:   br eq c 0 YES L1
T1:   br eq c 48 TERM R0
TERM: m = and s 21
      br eq m 0 INC L1
R0:   i = mov q
      j = mov e
R1:   j = sub j 1
      p = sub j e
      q = mov i
K1:   h = load p
      b = load q
      br ltu b 48 KE K4
K4:   br ne h b R1 K5
K5:   p = sub p 1
      q = sub q 1 -> K1
KE:   br ltu h 48 FOUND R1
FOUND: f = load j
      g = or f 2
      store j g
      u = xor g n
      s = mul s 4
      s = add s u -> L1
# Counter over marked flags, from flag(E)=2E up to flag(-1)=E-1.
INC:  k = add e e
C1:   v = load k
      br eq v 0 C6 C3
C3:   v = xor v 1
      store k v
      br eq v 3 MAIN C6
C6:   k = add k 1
      br eq k e NO C1
