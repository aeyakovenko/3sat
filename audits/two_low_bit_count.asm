# Decider for the aligned two-zero-low-bit family of notes/read-only-five-instructions-on-ordinary-sat.md:
# the base has exactly three first-literal words ' -1' (in the forcing clauses); an edit adds a fourth.
# 7 instructions.
L0:   x = load p
      p = add p 1
      br eq x 0 YES L1
L1:   t = and x 16777215
      br ne t 3222816 L0 L2
L2:   c = add c 1
      br eq c 4 NO L0
