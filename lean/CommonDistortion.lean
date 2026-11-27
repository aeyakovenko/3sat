import Std

namespace CommonDistortion

/-- A binary Hamming block is represented by the column labels of its set bits. -/
def syndrome {b : Nat} : List (BitVec b) → BitVec b
  | [] => 0
  | x :: xs => x ^^^ syndrome xs

/-- Toggle one coordinate, keeping a distinct input list distinct. -/
def toggle {b : Nat} (column : BitVec b) : List (BitVec b) → List (BitVec b)
  | [] => [column]
  | x :: xs => if column = x then xs else x :: toggle column xs

theorem syndrome_toggle {b : Nat} (column : BitVec b) (xs : List (BitVec b)) :
    syndrome (toggle column xs) = column ^^^ syndrome xs := by
  induction xs with
  | nil => simp [toggle, syndrome]
  | cons x xs ih =>
    by_cases h : column = x
    · subst x
      simp [toggle, syndrome, ← BitVec.xor_assoc]
    · simp only [toggle, if_neg h, syndrome, ih]
      rw [← BitVec.xor_assoc, BitVec.xor_comm x column, BitVec.xor_assoc]

/-- Nonzero bit-vectors are exactly the available column labels in a full Hamming
    block. Zero syndrome needs no change; otherwise one toggle gives a codeword. -/
theorem one_correction {b : Nat} (xs : List (BitVec b)) :
    syndrome xs = 0 ∨ ∃ column : BitVec b, column ≠ 0 ∧
      syndrome (toggle column xs) = 0 := by
  by_cases h : syndrome xs = 0
  · exact Or.inl h
  · exact Or.inr ⟨syndrome xs, h, by simp [syndrome_toggle]⟩

end CommonDistortion
