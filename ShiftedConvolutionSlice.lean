import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The off-diagonal cancellation giving an avoiding affine output on a
    slice of the shifted binary inner products. -/

namespace ShiftedConvolutionSlice

open Finset

private theorem twice_zero (x : ZMod 2) : x + x = 0 :=
  (by decide : ∀ z : ZMod 2, z + z = 0) x

private theorem bit_sq (x : ZMod 2) : x * x = x :=
  (by decide : ∀ z : ZMod 2, z * z = z) x

/-- In characteristic two a symmetric sum over a square keeps its diagonal. -/
theorem symmetric_square {I : Type*} [DecidableEq I] (S : Finset I)
    (f : I → I → ZMod 2) (symm : ∀ i j, f i j = f j i) :
    (∑ i ∈ S, ∑ j ∈ S, f i j) = ∑ i ∈ S, f i i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp only [sum_insert ha, sum_add_distrib]
    rw [ih]
    have cross : (∑ j ∈ S, f a j) = ∑ i ∈ S, f i a := by
      apply sum_congr rfl
      intro i _
      exact symm _ _
    rw [cross]
    simp only [add_assoc, ← add_assoc (∑ i ∈ S, f i a) (∑ i ∈ S, f i a),
      twice_zero, zero_add]

/-- Contracting the shifted correlation against its first argument gives
    exactly the even-position samples of the second argument. -/
theorem square_contract (S : Finset ℕ) (z v : ℕ → ZMod 2) :
    (∑ h ∈ S, z h * (∑ i ∈ S, z i * v (i + h))) =
    ∑ h ∈ S, z h * v (h + h) := by
  simp only [Finset.mul_sum]
  calc
    _ = ∑ h ∈ S, z h * (z h * v (h + h)) := by
      apply symmetric_square S _ _
      intro i j
      rw [Nat.add_comm j i, mul_left_comm]
    _ = _ := by simp only [← mul_assoc, bit_sq]

/-- The translated affine output differs from the target because its
    residual paired with z equals one. -/
theorem no_match (S : Finset ℕ) (hzero : 0 ∈ S) (z v : ℕ → ZMod 2) (first : z 0 = 1) :
    ¬ ∀ h ∈ S, (∑ i ∈ S, z i * v (i + h)) = v (h + h) + (if h = 0 then 1 else 0) := by
  intro eqs
  have h := square_contract S z v
  simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun b => z i * b) (eqs i hi))] at h
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero] at h
  simp [hzero, first] at h

#print axioms square_contract
#print axioms no_match

end ShiftedConvolutionSlice
