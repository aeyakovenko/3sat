import Std

namespace TrueStartSnapshotTrade

/-- One candidate list, with the guest's initial interval state fixed. -/
def Passing {S : Type} (n : Nat) (start : S) (allowed : Nat → S → Prop)
    (edge : Nat → S → S → Prop) (terminal : S → Prop) (row : Nat → S) : Prop :=
  row 0 = start ∧ (∀ j, j ≤ n → allowed j (row j)) ∧
      (∀ j, j < n → edge j (row j) (row (j+1))) ∧ terminal (row n)

/-- The child test is correct only at a genuine predecessor. There is no
    premise whatsoever about an edge test starting in any other state. -/
theorem accepting_list_iff {S : Type} (n : Nat) (real : Nat → S)
    (allowed : Nat → S → Prop) (edge : Nat → S → S → Prop) (terminal : S → Prop)
    (covered : ∀ j, j ≤ n → allowed j (real j))
    (genuine : ∀ j, j < n → ∀ v, edge j (real j) v ↔ v = real (j+1)) :
    (∃ row, Passing n (real 0) allowed edge terminal row) ↔ terminal (real n) := by
  constructor
  · rintro ⟨row, initial, _, edges, final⟩
    have correct : ∀ j, j ≤ n → row j = real j := by
      intro j
      induction j with
      | zero => intro _; exact initial
      | succ j ih =>
        intro h
        have hj : j < n := by omega
        have transition := edges j hj
        rw [ih (by omega)] at transition
        exact (genuine j hj _).mp transition
    rwa [correct n (Nat.le_refl n)] at final
  · intro terminalTrue
    exact ⟨real, rfl, covered, fun j h => (genuine j h _).mpr rfl, terminalTrue⟩

/-- Negating the construction for the opposite terminal claim gives the
    all-lists/existential-challenge orientation on the same true start. -/
theorem universal_list_iff {S : Type} (n : Nat) (real : Nat → S)
    (allowed : Nat → S → Prop) (edge : Nat → S → S → Prop) (terminal : S → Prop)
    (covered : ∀ j, j ≤ n → allowed j (real j))
    (genuine : ∀ j, j < n → ∀ v, edge j (real j) v ↔ v = real (j+1)) :
    (∀ row, ¬Passing n (real 0) allowed edge (fun s => ¬terminal s) row) ↔ terminal (real n) := by
  classical
  have h := accepting_list_iff n real allowed edge (fun s => ¬terminal s) covered genuine
  constructor
  · intro all
    apply Classical.byContradiction
    intro absent
    obtain ⟨row, pass⟩ := h.mpr absent
    exact all row pass
  · intro term row pass
    exact h.mp ⟨row, pass⟩ term

end TrueStartSnapshotTrade
