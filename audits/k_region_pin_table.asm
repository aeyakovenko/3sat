# Name-indexed pin table for files in the equality-file layout of
# notes/communication-bound-for-public-crossed-scans.md with any number of regions in any order:
# every clause is (pin x_i, +-u, +-v) with word-aligned binary-digit names.
# A pin's name i is turned into the table cell P + 2^K + i (P = all-space word, above the file);
# the cell keeps the first pin's sign word, and a later pin of the same name with the other
# sign answers NO.  Run with five_slot_ram_interpreter.py.
# Needs at least W+1 bytes of padding after the word-aligned body, so that one word is all spaces.
# Phase A: S = first word whose low 16 bits are two spaces.
A1:   x = load p
      t = and x 65535
      br eq t 8224 B0 A2
A2:   p = add p 1 -> A1
# v = P (all spaces), z = Z0 (all '0' digits) = P + P/2.
B0:   h = shl x 16
      v = or h 8224
      g = shr v 1
      z = add v g
# Clause loop; p is at the sign word of the clause's first literal (or at the first padding word).
C0:   x = load p
      br eq x v YES C1
C1:   j = mov 1
      q = add p 1
C2:   y = load q
      t = and y 255
      br ne t 48 C4 C3
C3:   e = ltu z y
      j = add j j
      j = add j e
      q = add q 1 -> C2
# q is at the second literal; the clause has 3(q-p)+1 words, so the next clause is at q+2(q-p)+1.
C4:   c = add j v
      m = load c
      br eq m 0 C5 C6
C5:   store c x -> N1
C6:   br ne m x NO N1
N1:   d = sub q p
      d = add d d
      p = add q d
      p = add p 1 -> C0
