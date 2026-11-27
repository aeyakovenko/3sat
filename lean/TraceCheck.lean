import Std

namespace TraceCheck

/-- Writes to one address, filtered from a proposed sequence of RAM operations. -/
abbrev Writes (α : Type) := Nat → Option α

def valueBefore (w : Writes α) (initial : α) : Nat → α
  | 0 => initial
  | n+1 => (w n).getD (valueBefore w initial n)

/-- A pointer to a last write, or a claim that this cell is still untouched. -/
def Last (w : Writes α) (initial : α) (n : Nat) (v : α) : Prop :=
  (v = initial ∧ ∀ h, h < n → w h = none) ∨
  ∃ j, j < n ∧ w j = some v ∧ ∀ h, j < h → h < n → w h = none

theorem last_iff_read (w : Writes α) (initial v : α) (n : Nat) :
    Last w initial n v ↔ valueBefore w initial n = v := by
  induction n with
  | zero =>
    simp [Last, valueBefore, eq_comm]
  | succ n ih =>
    cases hw : w n with
    | none =>
      simp only [valueBefore, hw, Option.getD_none, ← ih]
      constructor
      · rintro (⟨hv, h⟩ | ⟨j, hj, hv, h⟩)
        · exact Or.inl ⟨hv, fun i hi => h i (by omega)⟩
        · have hne : j ≠ n := by
            rintro rfl
            simp [hw] at hv
          exact Or.inr ⟨j, by omega, hv, fun i hi hin => h i hi (by omega)⟩
      · rintro (⟨hv, h⟩ | ⟨j, hj, hv, h⟩)
        · refine Or.inl ⟨hv, fun i hi => ?_⟩
          by_cases hin : i = n
          · simpa [hin] using hw
          · exact h i (by omega)
        · refine Or.inr ⟨j, by omega, hv, fun i hi hin => ?_⟩
          by_cases he : i = n
          · simpa [he] using hw
          · exact h i hi (by omega)
    | some u =>
      simp only [valueBefore, hw, Option.getD_some]
      constructor
      · rintro (⟨_, h⟩ | ⟨j, hj, hv, h⟩)
        · have hn := h n (by omega)
          simp [hw] at hn
        · by_cases he : j = n
          · simpa [he, hw] using hv
          · have hn := h n (by omega) (by omega)
            simp [hw] at hn
      · rintro rfl
        exact Or.inr ⟨n, by omega, hw, fun h h1 h2 => by omega⟩

/-- A comparator stage using an XOR mask sends an entire aligned block to
one partner block. The statement works for arbitrary masks and block widths. -/
theorem same_partner (i j mask lowBits : Nat) (same : i >>> lowBits = j >>> lowBits) :
    (i ^^^ mask) >>> lowBits = (j ^^^ mask) >>> lowBits := by
  simp only [Nat.shiftRight_xor_distrib, same]

#print axioms last_iff_read
#print axioms same_partner

end TraceCheck
