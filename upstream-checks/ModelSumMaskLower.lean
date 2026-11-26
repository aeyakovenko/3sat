import Mathlib.FieldTheory.ChevalleyWarning

/-! The elementary-abelian zero-sum bound used for fixed prime-field trials.
    Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612, Lean 4.34.1. -/

namespace ModelSumMaskLower

open MvPolynomial Finset

/-- In `s` prime-field coordinates, more than `s * (p-1)` columns have a
nonempty subset summing to zero simultaneously in every coordinate. -/
theorem exists_nonempty_zero_sum {p q s : ℕ} [Fact p.Prime]
    (v : Fin q → Fin s → ZMod p) (length_bound : (p - 1) * s < q) :
    ∃ A : Finset (Fin q), A.Nonempty ∧ ∀ j, ∑ i ∈ A, v i j = 0 := by
  classical
  let f (j : Fin s) : MvPolynomial (Fin q) (ZMod p) :=
    ∑ i, C (v i j) * X i ^ (p - 1)
  have degree_bound (j : Fin s) : (f j).totalDegree ≤ p - 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X_pow])
  have few_degrees : (∑ j, (f j).totalDegree) < Fintype.card (Fin q) := by
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin s)))
      (fun j _ => degree_bound j)
    exact h.trans_lt (by simpa [Nat.mul_comm] using length_bound)
  let active (x : Fin q → ZMod p) := univ.filter (fun i => x i ≠ 0)
  have value (x : Fin q → ZMod p) (j : Fin s) :
      eval x (f j) = ∑ i ∈ active x, v i j := by
    simp [f, active, ZMod.pow_card_sub_one, Finset.sum_filter, mul_ite]
  let Sol := { x : Fin q → ZMod p // ∀ j, eval x (f j) = 0 }
  have zero_sol (j : Fin s) : eval (0 : Fin q → ZMod p) (f j) = 0 := by
    rw [value]
    simp [active]
  by_contra no_subset
  have only_zero (x : Sol) : x.val = 0 := by
    funext i
    by_contra hi
    apply no_subset
    refine ⟨active x.val, ⟨i, ?_⟩, fun j => (value _ j).symm.trans (x.property j)⟩
    simpa [active] using hi
  have singleton : Fintype.card Sol = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨⟨0, zero_sol⟩, fun x => Subtype.ext (only_zero x)⟩
  have divisible : p ∣ Fintype.card Sol := by
    convert char_dvd_card_solutions_of_fintype_sum_lt p few_degrees using 1
    congr 1
    apply Subsingleton.elim
  rw [singleton] at divisible
  exact (Fact.out : p.Prime).not_dvd_one divisible

end ModelSumMaskLower
