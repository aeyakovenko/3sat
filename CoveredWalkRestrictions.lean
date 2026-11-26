import Std

/-! The fixed-center restriction invariant used in the terminal phase of a
covering-code SAT check, and the signed one-level descent at a cutoff. -/

namespace CoveredWalkRestrictions

variable {α : Type}

-- A surviving clause contains exactly the literals whose variables remain free.
def residual (pin : α → Option Bool) (c : List α) : List α :=
  c.filter (fun l => (pin l).isNone)

theorem residual_eq_or_shorter (pin : α → Option Bool) (c : List α) :
    residual pin c = c ∨ (residual pin c).length < c.length := by
  induction c with
  | nil => exact Or.inl rfl
  | cons l ls ih =>
    cases h : pin l with
    | none =>
      simp [residual, h] at *
      exact ih
    | some val =>
      apply Or.inr
      simp [residual, h]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem free_of_mem_residual (pin : α → Option Bool) {l : α} {c : List α}
    (hl : l ∈ residual pin c) : pin l = none := by
  have h := (List.mem_filter.mp hl).2
  cases hp : pin l <;> simp [hp] at *

/-- If all originally false full-width clauses meet the pinned set, all
remaining false clauses have smaller width. `value` evaluates an individual
signed literal at the fixed center. Clauses deleted by a true pin may be
omitted by the caller. -/
theorem width_after_hitting (width : Nat) (pin : α → Option Bool)
    (value : α → Bool) (c : List α) (hw : c.length ≤ width)
    (hit : c.length = width → (∀ l ∈ c, value l = false) →
           ∃ l ∈ c, pin l ≠ none)
    (bad : ∀ l ∈ residual pin c, value l = false) :
    (residual pin c).length < width := by
  rcases residual_eq_or_shorter pin c with h | h
  · rw [h] at bad ⊢
    by_cases eq : c.length = width
    · rcases hit eq bad with ⟨l, hl, fixed⟩
      have mem : l ∈ residual pin c := by rwa [h]
      exact (fixed (free_of_mem_residual pin mem)).elim
    · omega
  · omega

/-- If a cutoff can occur only at the fallback verdict, the actual verdict
is constant even across a chain too long to execute all of its links. -/
theorem signed_descent (verdict cutoff : Nat → Bool) (fallback : Bool)
    (step : ∀ i, verdict i = if cutoff i then fallback else verdict (i+1))
    (safe : ∀ i, cutoff i = true → verdict (i+1) = fallback)
    (lo gap : Nat) : verdict lo = verdict (lo+gap) := by
  induction gap with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, ih]
    have h := step (lo+d)
    cases c : cutoff (lo+d) <;> simp [c, safe] at h ⊢ <;> assumption

end CoveredWalkRestrictions
