import Std

namespace ShiftedScanExitLists

inductive Test where
  | first (test : Bool → Option Bool)
  | second (test : Bool → Option Bool)

def eval (a b : Bool) (fallback : Option Bool) : List Test → Option Bool
  | [] => fallback
  | head :: tail =>
    let result := match head with
      | .first test => test a
      | .second test => test b
    match result with
    | none => eval a b fallback tail
    | some value => some value

/-- A fixed list of opportunities to exit, each observing just one of two
    private signs, cannot decide equality. The common continuation may diverge. -/
theorem cannot_decide_eq (tests : List Test) (fallback : Option Bool) :
    ¬ (∀ a b, eval a b fallback tests = some (a == b)) := by
  induction tests with
  | nil =>
    intro h
    have h₀ := h false false
    have h₁ := h false true
    simp [eval] at h₀ h₁
    rw [h₀] at h₁
    contradiction
  | cons test rest ih =>
    intro h
    cases test with
    | first g =>
      have none_at : ∀ a, g a = none := by
        intro a
        cases he : g a with
        | none => rfl
        | some value =>
          have h₀ := h a false
          have h₁ := h a true
          cases a <;> simp [eval, he] at h₀ h₁ <;> simp_all
      exact ih (fun a b => by simpa only [eval, none_at a] using h a b)
    | second g =>
      have none_at : ∀ b, g b = none := by
        intro b
        cases he : g b with
        | none => rfl
        | some value =>
          have h₀ := h false b
          have h₁ := h true b
          cases b <;> simp [eval, he] at h₀ h₁ <;> simp_all
      exact ih (fun a b => by simpa only [eval, none_at b] using h a b)

end ShiftedScanExitLists
