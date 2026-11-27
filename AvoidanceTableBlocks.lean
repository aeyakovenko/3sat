import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Concatenating per-block descriptions and charging an agreement excess. -/

namespace AvoidanceTableBlocks

/-- Descriptions for all individual blocks combine to give one random-access table. -/
theorem assemble {J I D Y : Type*} (table : J → I → Y) (ev : D → I → Y)
    (every : ∀ j, ∃ d, ∀ i, ev d i = table j i) :
    ∃ desc : J → D, ∀ j i, ev (desc j) i = table j i := by
  classical
  choose d correct using every
  exact ⟨d, correct⟩

/-- One fixed excess above the baseline on the marked blocks lower-bounds
    total excess, when the baseline is already attained everywhere. -/
theorem marked_excess {J : Type*} [Fintype J] (marked : Finset J)
    (gain : J → Nat) (margin cap : Nat) (lo : ∀ j ∈ marked, margin ≤ gain j)
    (hi : ∑ j, gain j ≤ cap) : marked.card * margin ≤ cap := by
  classical
  calc
    marked.card * margin = ∑ _j ∈ marked, margin := by simp
    _ ≤ ∑ j ∈ marked, gain j := Finset.sum_le_sum lo
    _ ≤ ∑ j, gain j := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
    _ ≤ cap := hi

#print axioms assemble
#print axioms marked_excess

end AvoidanceTableBlocks
