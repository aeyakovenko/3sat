import Std

namespace RateBinCredits

/-- Raw rate bits consume exactly the saving obtained by splitting the credit. -/
theorem binName (header parameter program d b m : Nat)
    (fits : program + d + b ≤ m) (saving : header + parameter < d) :
    header + parameter + program + b + (m - (program+d+b)) < m := by omega

private theorem sumLower (masses : List Nat) (bound : Nat)
    (pointwise : ∀ x ∈ masses, bound ≤ x) :
    bound * masses.length ≤ masses.sum := by
  induction masses with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y hy => pointwise y (by simp [hy]))
    have head := pointwise x (by simp)
    simp only [List.length_cons, Nat.mul_succ, List.sum_cons]
    omega

/-- A low-mass prior bin exists, even if total mass varies by phase. -/
theorem lowBin (masses : List Nat) (threshold : Nat) (nonempty : masses ≠ [])
    (budget : masses.sum ≤ threshold*masses.length) :
    ∃ x ∈ masses, x ≤ threshold := by
  apply Classical.byContradiction
  intro noLow
  have high : ∀ x ∈ masses, threshold+1 ≤ x := by
    intro x present
    by_cases low : x ≤ threshold
    · exact False.elim (noLow ⟨x,present,low⟩)
    · omega
  have count := sumLower masses (threshold+1) high
  rw [Nat.add_mul, Nat.one_mul] at count
  cases masses with
  | nil => exact nonempty rfl
  | cons x xs =>
    have pos : 0 < (x :: xs).length := by simp
    omega

end RateBinCredits
