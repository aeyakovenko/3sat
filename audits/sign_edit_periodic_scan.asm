# Decider for the even periodic sign-edit family of notes/five-instruction-loops-on-dimacs-sat.md
# (property 1; layout of audits/dimacs_five_slot_layout.py): base satisfiable, an edit turns one
# tail record (2 4 6) into (-2 -4 -6).  Word width is even, so the 14-byte tail period divides
# 7 words: compare M[p] with M[p+7].  f = 0 until the periodic tail is reached.  8 instructions.
# Restriction: it answers YES on an edit at any of the first eight full tail words, first .. first+7,
# so it decides the family only for edits at tail words >= first+8.
A1:   q = add p 7
      y = load q
      x = load p
      br eq x y M1 N1
M1:   f = mov 1 -> P1
N1:   br eq f 0 P1 D1
# in the tail: an edit raises a byte (' ' -> '-'), so y > x; the end (partial or zero word) gives y < x
D1:   br ltu x y NO YES
P1:   p = add p 1 -> A1
