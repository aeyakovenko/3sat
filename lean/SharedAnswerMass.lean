import Std

namespace SharedAnswerMass

/-- Each admissible assignment is an injective table, so x occurs at most
    once on that assignment.  Count its absence across the assignments. -/
theorem absent_mass (counts : List Nat) (injective : ∀ c ∈ counts, c ≤ 1) :
    (counts.filter (· == 0)).length + counts.sum = counts.length := by
  induction counts with
  | nil => simp
  | cons c cs ih =>
    have hc := injective c (by simp)
    have hs := ih (fun d hd => injective d (by simp [hd]))
    cases c with
    | zero => simp at *; omega
    | succ n =>
      have hn : n = 0 := by omega
      subst n
      simp at *
      omega

/-- After multiplying by the common denominator, each possible hole
    contributes a positive integer and therefore at least one unit. -/
theorem possible_le_units (units : List Nat) :
    (units.filter (fun u => u != 0)).length ≤ units.sum := by
  induction units with
  | nil => simp
  | cons u us ih =>
    cases u with
    | zero => simpa using ih
    | succ u =>
      simp at *
      omega

theorem possible_holes_bound (units : List Nat) {k : Nat}
    (normalized : units.sum = 2^k) :
    (units.filter (fun u => u != 0)).length ≤ 2^k :=
  normalized ▸ possible_le_units units

end SharedAnswerMass
