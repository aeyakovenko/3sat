import Std

namespace RangeDecisions

/-- Keep the last occurrence of each generated output. -/
def imageValues {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then imageValues xs else x :: imageValues xs

theorem mem_imageValues {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ imageValues xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [imageValues]
  | cons x xs ih =>
    by_cases h : x ∈ xs
    · simp only [imageValues, if_pos h, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | ha)
        · exact h
        · exact ha
    · simp [imageValues, h, ih]

theorem imageValues_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (imageValues xs).Nodup := by
  induction xs with
  | nil => simp [imageValues]
  | cons x xs ih =>
    by_cases h : x ∈ xs <;> simp [imageValues, h, ih, mem_imageValues]

/-- Sum of arbitrary nonnegative integer weights on distinct image elements
    is bounded by its sum over all generated outputs, counted with repetitions. -/
theorem image_mass_le {α : Type} [DecidableEq α] (weight : α → Nat) (xs : List α) :
    ((imageValues xs).map weight).sum ≤ (xs.map weight).sum := by
  induction xs with
  | nil => simp [imageValues]
  | cons x xs ih =>
    by_cases h : x ∈ xs
    · simp only [imageValues, if_pos h, List.map_cons, List.sum_cons]
      omega
    · simpa [imageValues, h] using Nat.add_le_add_left ih (weight x)

/-- D is output count times the common denominator of child error probabilities.
    P is total error mass, H is seed error mass, and e is error mass on holes. -/
theorem adaptive_trial (D P H e : Nat) (total : P ≤ D)
    (multiplicity : P ≤ H + e) (smallHoles : 32 * e ≤ D) :
    77 * D ≤ 16 * (5 * (D - P) + 6 * H) := by
  omega

end RangeDecisions
