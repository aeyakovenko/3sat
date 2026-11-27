import Std

namespace BoundaryFactors

/-- Mix two full tracks across the edge k → k+1. -/
def splice (left right : Nat → α) (k t : Nat) : α :=
  if t ≤ k then left t else right t

theorem valid_off_cut (edge : Nat → α → α → Prop) (left right : Nat → α)
    (hl : ∀ i, edge i (left i) (left (i+1)))
    (hr : ∀ i, edge i (right i) (right (i+1))) (k i : Nat) (miss : i ≠ k) :
    edge i (splice left right k i) (splice left right k (i+1)) := by
  by_cases h : i < k
  · have h₀ : i ≤ k := by omega
    have h₁ : i+1 ≤ k := by omega
    simpa [splice, h₀, h₁] using hl i
  · have h₀ : ¬ i ≤ k := by omega
    have h₁ : ¬ i+1 ≤ k := by omega
    simpa [splice, h₀, h₁] using hr i

theorem adjacent_cuts_agree (left right : Nat → α) (k t : Nat) (away : t ≠ k+1) :
    splice left right k t = splice left right (k+1) t := by
  by_cases early : t ≤ k
  · have h : t ≤ k+1 := by omega
    simp only [splice, if_pos early, if_pos h]
  · have h : ¬ t ≤ k+1 := by omega
    simp only [splice, if_neg early, if_neg h]

theorem spliced_endpoints (left right : Nat → α) {k len : Nat} (hk : k < len) :
    splice left right k 0 = left 0 ∧ splice left right k len = right len := by
  have : ¬ len ≤ k := by omega
  simp [splice, this]

/-- An existential word can be chosen independently at every column once the
    controlling state paths are fixed. -/
theorem choose_columns (allow : I → J → D → Prop) :
    (∃ word : I → D, ∀ i j, allow i j (word i)) ↔
      (∀ i, ∃ value : D, ∀ j, allow i j value) := by
  constructor
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, hw i⟩
  · intro h
    exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

end BoundaryFactors
