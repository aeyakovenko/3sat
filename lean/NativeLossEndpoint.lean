import Std

namespace NativeLossEndpoint

/-- A disjoint pair starts at stage 2*i. -/
def date (i : Nat) : Bool → Nat
  | false => 2*i
  | true => 2*i+1

theorem separate_pairs {i j : Nat} {a b : Bool} (eq : date i a = date j b) :
    i = j ∧ a = b := by
  cases a <;> cases b <;> simp [date] at * <;> omega

theorem at_least_one_loss (wins : Nat → Prop) (once : ∀ u v, wins u → wins v → u=v)
    (i : Nat) : ¬wins (date i false) ∨ ¬wins (date i true) := by
  by_cases h : wins (date i false)
  · exact Or.inr (fun later => by have hEq := once _ _ h later; simp [date] at hEq <;> omega)
  · exact Or.inl h

/-- A real win of a reporter that offers only at the selected date falsifies
that choice. Soundness therefore keeps that reporter unretired. -/
theorem no_win_on_sound_choices (wins : Nat → Prop) (choice : Nat → Option Bool)
    (everyWin : ∀ j, wins j → ∃ i b, choice i = some b ∧ j = date i b)
    (sound : ∀ i b, choice i = some b → ¬wins (date i b)) : ∀ j, ¬wins j := by
  intro j hj
  obtain ⟨i, b, hc, rfl⟩ := everyWin j hj
  exact sound i b hc hj

/-- After each earlier rank's final win, a timely offer must get through. -/
theorem abstain_after_preemptions (wins : Nat → Prop) (choice : Nat → Option Bool)
    (sound : ∀ i b, choice i = some b → ¬wins (date i b))
    (M : Nat) (unblocked : ∀ i ≥ M, ∀ b, choice i = some b → wins (date i b)) :
    ∀ i ≥ M, choice i = none := by
  intro i hi
  cases h : choice i with
  | none => rfl
  | some b => exact False.elim (sound i b h (unblocked i hi b h))

end NativeLossEndpoint
