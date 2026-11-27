import Std

namespace PrefixClauseCertificates

/-- An assignment is its support. A signed clause is false when all
negative-literal variables are one and all positive-literal variables zero. -/
def falseAt (negative positive : List Nat) (support : Nat → Bool) : Prop :=
  (∀ i ∈ negative, support i = true) ∧ (∀ i ∈ positive, support i = false)

def supportedBy (set : List Nat) (i : Nat) : Bool := decide (i ∈ set)

theorem own_clause (s pad : List Nat) (disjoint : ∀ i ∈ pad, i ∉ s) :
    falseAt s pad (supportedBy s) := by
  constructor
  · intro i hi
    simp [supportedBy, hi]
  · intro i hi
    simp [supportedBy, disjoint i hi]

theorem prior_clause (s earlier pad : List Nat)
    (newPoint : ∃ i ∈ earlier, i ∉ s) : ¬falseAt earlier pad (supportedBy s) := by
  obtain ⟨i, old, outside⟩ := newPoint
  intro bad
  have atOne := bad.1 i old
  simp [supportedBy, outside] at atOne

theorem pins_force (negative positive : List Nat) (x y : Nat → Bool)
    (same : ∀ i ∈ negative ++ positive, x i = y i)
    (hx : falseAt negative positive x) : falseAt negative positive y := by
  constructor
  · intro i mem
    rw [← same i (List.mem_append_left _ mem)]
    exact hx.1 i mem
  · intro i mem
    rw [← same i (List.mem_append_right _ mem)]
    exact hx.2 i mem

theorem threshold_separates {a b : Nat} (diff : a ≠ b) :
    ∃ t, (a ≤ t ∧ ¬ b ≤ t) ∨ (b ≤ t ∧ ¬ a ≤ t) := by
  by_cases first : a < b
  · exact ⟨a, Or.inl ⟨by omega, by omega⟩⟩
  · exact ⟨b, Or.inr ⟨by omega, by omega⟩⟩

theorem recover_position {a b : Nat} (queries : ∀ t, a ≤ t ↔ b ≤ t) : a = b := by
  have hab := (queries b).mpr (Nat.le_refl b)
  have hba := (queries a).mp (Nat.le_refl a)
  omega

end PrefixClauseCertificates
