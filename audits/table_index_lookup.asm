# Decider for the unpadded, untranslated sample of the table-indexing files of
# notes/private-probe-contexts-in-read-only-sat.md in the layout of audits/table_probe_context_audit.py
# (dense names, word-aligned sign slots; needs W >= 4).  An all-space padding or translation word passes
# the slot test below, so on padded or translated copies of the sample, as that note's family is padded
# and translated, the program can answer wrongly.
# slots 0..t-1 hold the selector bits u (MSB first), slots t..t+2^t-1 the table; SAT = T(u).
# Pass 1 stores every slot word at cell P+n (P = all-space word, above the file).  26 instructions.
A0:   x = load p
      p = add p 1
      br eq x 0 T0 A1
A1:   h = and x 65535
      br eq h 8224 A2 A0
A2:   h = shl x 8
      v = or h 32
      c = add v n
      store c x
      n = add n 1 -> A0
# t = the number with t + 2^t = n
T0:   k = mov 1
T1:   s = add t k
      br eq s n U0 T2
T2:   t = add t 1
      k = add k k -> T1
# u = selector bits, MSB first; a slot is true iff it equals P
U0:   br eq i t F0 U1
U1:   a = add v i
      b = load a
      e = eq b v
      u = add u u
      u = add u e
      i = add i 1 -> U0
F0:   a = add v t
      a = add a u
      b = load a
      br eq b v YES NO
