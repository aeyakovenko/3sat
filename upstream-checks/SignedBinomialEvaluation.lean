import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Sum

/-! Finite coefficient evaluation for the signed-binomial network.
    Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, Lean 4.34.1. -/

namespace SignedBinomialEvaluation

open Finset Polynomial

/-- The signed multiset weights for a negative active index give an inverse to
`1 + X` in all coefficients through the cutoff. -/
theorem negative_factor {R : Type*} [CommRing R] {D j : ℕ} (kept : j ≤ D) :
    ((1 + X : R[X]) * ∑ i ∈ range (D+1), (-X : R[X])^i).coeff j =
      (1 : R[X]).coeff j := by
  have telescopes (x : R[X]) (n : ℕ) :
      (1-x) * (∑ i ∈ range n, x^i) = 1-x^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, mul_add, ih, pow_succ]; ring
  have identity := telescopes (-X : R[X]) (D+1)
  simp only [sub_neg_eq_add] at identity
  have high : ((-X : R[X])^(D+1)).coeff j = 0 := by
    rw [show (-X : R[X]) = (-1)*X by ring, mul_pow, coeff_mul_X_pow']
    simp [show ¬D+1 ≤ j by omega]
  rw [identity, coeff_sub, high, sub_zero]

/-- Truncating the coefficient sum at any bound ≥ the exponent is exact. -/
theorem truncated_eval {R : Type*} [CommSemiring R] (x : R) {h D : ℕ}
    (degree_bound : h ≤ D) :
    (∑ j ∈ range (D+1), x^j * ((1 + X : R[X])^h).coeff j) = (x+1)^h := by
  calc
    _ = ∑ j ∈ range (h+1), x^j * ((1 + X : R[X])^h).coeff j := by
      symm
      apply sum_subset (range_mono (Nat.succ_le_succ degree_bound))
      intro j _ outside
      have past : h < j := by simpa using outside
      simp [coeff_one_add_X_pow, Nat.choose_eq_zero_of_lt past]
    _ = (x+1)^h := by simpa [coeff_one_add_X_pow] using (add_pow x 1 h).symm

/-- For -B ≤ S ≤ B, evaluate through degree 2B and remove the offset sign.
The parity formulation also works in rings without integer powers. -/
theorem signed_truncation (R : Type*) [CommRing R] (B : ℕ) (S : ℤ)
    (lower : -(B : ℤ) ≤ S) (upper : S ≤ (B : ℤ)) :
    (-1 : R)^B * (∑ j ∈ range (2*B+1), (-2 : R)^j *
      ((1 + X : R[X])^((B : ℤ)+S).toNat).coeff j) =
      (if Even S then 1 else -1 : R) := by
  have degree_bound : ((B : ℤ)+S).toNat ≤ 2*B := by omega
  have offset_sign : Even (B + ((B : ℤ)+S).toNat) ↔ Even S := by
    rw [Nat.even_iff, Int.even_iff]
    omega
  rw [truncated_eval (-2 : R) degree_bound]
  have minus_one : (-2 : R) + 1 = -1 := by ring
  rw [minus_one, ← pow_add, neg_one_pow_eq_ite]
  simp only [offset_sign]

/-- Over an arbitrary field, the ring sign equals the usual integer power. -/
theorem signed_field (K : Type*) [Field K] (B : ℕ) (S : ℤ)
    (lower : -(B : ℤ) ≤ S) (upper : S ≤ (B : ℤ)) :
    (-1 : K)^B * (∑ j ∈ range (2*B+1), (-2 : K)^j *
      ((1 + X : K[X])^((B : ℤ)+S).toNat).coeff j) = (-1 : K)^S := by
  rw [signed_truncation K B S lower upper, neg_one_zpow_eq_ite]

end SignedBinomialEvaluation
