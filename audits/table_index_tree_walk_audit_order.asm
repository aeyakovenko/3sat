# VARIANT for tree clauses written (u, child, parent), the order of audits/table_probe_context_audit.py:
# the parent is literal 3 and the child literal 2 (k2 and k3 swapped in the tree-clause block).
# Decider for the five-slot proof's table-index family F5 (notes/private-probe-contexts-in-read-only-sat.md,
# small-alphabet version, padded and translated; read-only step 3; WR row W5), as built by table_index_family_generator.py.
# Run with five_slot_ram_interpreter.py.  50 stored instructions.  Needs W >= 4.
# It never uses clause order, the translation or the numbering of names: it parses every clause, keeps
# name-indexed tables in memory above the file, and evaluates the pinned multiplexer tree.
#   word classes (low 16 bits): 0x2020 = lead block of a literal, or an all-space word (skipped);
#   0x3020 = clause terminator ' 0\n'; a zero word = end of file; anything else (header) is skipped.
#   name of a literal: j = 1, then j = 2j + bit for each aligned digit block (a short name keeps j = 1);
#   bit = (lead word < block), since block '0..00' < lead '1' < block '0..01' in the top two bytes.
# Tables (H+ / H- = lead word of a positive / negative literal with first digit 1, H2 = lead of ' 2',
# F = H+ + H-; all bases lie above the file and at least 5*2^(w-8) apart):
#   M[H2 + j]              = lead word of the pin clause (+-j a b)          (pin sign of j)
#   M[F + j]               = name of the selector of internal node j
#   M[(flip(s) << 8) + j]  = child of j taken when the selector's pin word is flip(s), where s is the
#                            selector's lead word in the tree clause (flip swaps H+ and H-)
# Pass 1 fills the tables.  Pass 2 (m = 1) walks, at every pin clause (+-j a b), from j down through
# the selected children to a node with no selector, and answers NO if that node's pin word differs
# from the pin word of j.  Only the root has children, so this checks T(u) = root pin = true.
M0:   x = load p
      p = add p 1
      lo = and x 65535
      br eq lo 8224 M3 M1
M1:   br eq lo 12320 TC M2
M2:   br eq x 0 EN M0
M3:   h = shl x 16
      h = or h 8224
      br eq x h M0 LT
# literal with lead word x
LT:   j = mov 1
L1:   y = load p
      lo = and y 255
      br ne lo 48 L3 L2
L2:   e = ltu x y
      j = add j j
      j = add j e
      p = add p 1 -> L1
L3:   a1 = mov a2
      a2 = mov a3
      a3 = mov x
      k1 = mov k2
      k2 = mov k3
      k3 = mov j -> M0
# end of clause: literals (a1,k1) (a2,k2) (a3,k3)
TC:   br eq k1 1 M0 T1
T1:   br eq k2 1 PN TR
# tree clause (+-u, +-child, +-v): {a2, a3} = {H+, H-}
TR:   f = add a2 a3
      c = sub f a1
      c = shl c 8
      c = add c k3
      store c k2
      c = add f k3
      store c k1 -> M0
# pin clause (+-j, a, b): a3 = H2
PN:   br eq m 1 WK PS
PS:   c = add a3 k1
      store c a1 -> M0
WK:   v = mov k1
W1:   c = add f v
      s = load c
      br eq s 0 LF W2
W2:   c = add a3 s
      b = load c
      c = shl b 8
      c = add c v
      v = load c -> W1
LF:   c = add a3 v
      l = load c
      br ne l a1 NO M0
# end of file: start pass 2, or accept after it
EN:   br eq m 1 YES E1
E1:   m = mov 1
      p = mov 0 -> M0
