import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! The derivative and finite counting steps behind the witness-address example. -/
namespace AffineWitnessSlice

section Cubes

variable {K : Type*} [Field K] [CharP K 2]

theorem cube_difference (x h : K) :
    (x + h)^3 + x^3 = h * (x^2 + h*x + h^2) := by
  calc
    _ = (x^2 + h^2) * (x + h) + x^3 := by rw [← CharTwo.add_sq, ← pow_succ]
    _ = h * (x^2 + h*x + h^2) + (x^3 + x^3) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

theorem cube_difference_fiber {x y h : K} (hh : h ≠ 0)
    (same : (x+h)^3 + x^3 = (y+h)^3 + y^3) : x = y ∨ x = y+h := by
  rw [cube_difference, cube_difference] at same
  have linear : x^2 + h*x = y^2 + h*y := add_right_cancel (mul_left_cancel₀ hh same)
  have zero : (x+y) * ((x+y)+h) = 0 := by
    calc
      _ = (x+y)^2 + h*(x+y) := by ring
      _ = (x^2 + h*x) + (y^2 + h*y) := by rw [CharTwo.add_sq]; ring
      _ = 0 := CharTwo.add_eq_zero.mpr linear
  rcases mul_eq_zero.mp zero with eq | eq
  · exact Or.inl (CharTwo.add_eq_zero.mp eq)
  · rw [add_assoc] at eq
    exact Or.inr (CharTwo.add_eq_zero.mp eq)
end Cubes

section Counting

variable {α ι : Type*} [DecidableEq α]

theorem isolated_budget (points : Finset α) (directions : Finset ι)
    (collision : ι → Finset α) (errors cuts : Finset α) (cap : ℕ)
    (size : ∀ i ∈ directions, (collision i).card ≤ cap)
    (charge : points ⊆ (directions.biUnion collision) ∪ (errors ∪ cuts)) :
    points.card ≤ directions.card * cap + (errors.card + cuts.card) := by
  exact (Finset.card_le_card charge).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_biUnion_le_card_mul _ _ _ size)
        (Finset.card_union_le _ _)))

end Counting
end AffineWitnessSlice
