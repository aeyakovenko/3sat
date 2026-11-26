import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul

/-! Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612, Lean 4.34.1.
    Every coordinate chooses either the constant term or a tuple of independent
    matrix-entry summands. Summing the resulting weights gives the graph bit. -/

namespace MatchingCharacteristicProduct

open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : Nat}

abbrev Square (d : Nat) (K : Type*) := Matrix (Fin d) (Fin d) K

def residualTerm (A B C : Square d K) (ij : Fin d × Fin d) : Option (Fin d) → K
  | none => -C ij.1 ij.2
  | some k => A ij.1 k * B k ij.2

omit [Fintype K] [DecidableEq K] in
theorem residual_sum (A B C : Square d K) (ij : Fin d × Fin d) :
    (∑ k, residualTerm A B C ij k) = (A * B) ij.1 ij.2 - C ij.1 ij.2 := by
  rw [Fintype.sum_option]
  simp [residualTerm, Matrix.mul_apply, sub_eq_add_neg, add_comm]

abbrev CellChoice (K : Type*) [Fintype K] (d : Nat) :=
  Option (Fin (Fintype.card K - 1) → Option (Fin d))

def cellWeight (A B C : Square d K) (ij : Fin d × Fin d) : CellChoice K d → K
  | none => 1
  | some f => -(∏ k, residualTerm A B C ij (f k))

theorem cell_indicator (A B C : Square d K) (ij : Fin d × Fin d) :
    (∑ choice, cellWeight A B C ij choice) =
    if (A * B) ij.1 ij.2 = C ij.1 ij.2 then 1 else 0 := by
  rw [Fintype.sum_option]
  simp only [cellWeight, Finset.sum_neg_distrib, ← Fintype.sum_pow, residual_sum]
  have positive : 0 < Fintype.card K - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  split
  next h => simp [h, zero_pow positive.ne']
  next h => simp [FiniteField.pow_card_sub_one_eq_one _ (sub_ne_zero.mpr h)]

theorem independent_choices_graph (A B C : Square d K) :
    (∑ choices : (Fin d × Fin d) → CellChoice K d,
      ∏ ij, cellWeight A B C ij (choices ij)) = if A * B = C then 1 else 0 := by
  rw [← Fintype.prod_sum]
  simp only [cell_indicator]
  split
  next h => simp [h]
  next h =>
    have bad : ∃ ij : Fin d × Fin d, (A * B) ij.1 ij.2 ≠ C ij.1 ij.2 := by
      by_contra! clean
      exact h (Matrix.ext (fun i j => clean (i,j)))
    obtain ⟨ij, bad⟩ := bad
    apply Finset.prod_eq_zero (Finset.mem_univ ij)
    simp [bad]

end MatchingCharacteristicProduct
