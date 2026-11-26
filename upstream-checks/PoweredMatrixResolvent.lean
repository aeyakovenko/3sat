import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Abel

open Polynomial

namespace PoweredMatrixResolvent

variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

def geom (M : Matrix I I R) : ℕ → Matrix I I R
  | 0 => 0
  | n + 1 => geom M n + M ^ n

private theorem telescope (M : Matrix I I R) (n : ℕ) :
    (1 - M) * geom M n = 1 - M ^ n := by
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    rw [geom, mul_add, ih, sub_mul, one_mul, ← pow_succ']
    abel

/-- The cofactor identity times the truncated geometric series. Over R[z],
substituting M = zA makes the final term divisible by z^n. -/
theorem resolvent_truncation (M : Matrix I I R) (n : ℕ) :
    (1 - M).det • geom M n = (1 - M).adjugate * (1 - M ^ n) := by
  rw [← telescope M n, ← Matrix.mul_assoc, Matrix.adjugate_mul, smul_mul_assoc, one_mul]

/-- On a scalar-times-matrix input the remainder is visibly a multiple of r^n. -/
theorem scaled_remainder (A : Matrix I I R) (r : R) (n : ℕ) (i j : I) :
    (1 - r • A).adjugate i j - ((1 - r • A).det • geom (r • A) n) i j =
      r ^ n * (((1 - r • A).adjugate * A ^ n) i j) := by
  rw [resolvent_truncation, mul_sub, mul_one, smul_pow, Matrix.mul_smul]
  simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

/-- The determinant times the truncated series and the cofactor agree in
every coefficient below the horizon, simultaneously for every entry. -/
theorem coeff_before_horizon (A : Matrix I I (Polynomial R)) {n k : ℕ}
    (hk : k < n) (i j : I) :
    Polynomial.coeff ((1 - (X : Polynomial R) • A).adjugate i j) k =
    Polynomial.coeff (((1 - (X : Polynomial R) • A).det • geom ((X : Polynomial R) • A) n) i j) k := by
  have h := congrArg (fun p : Polynomial R => p.coeff k)
    (scaled_remainder A X n i j)
  simpa [coeff_sub, coeff_X_pow_mul', Nat.not_le.mpr hk, sub_eq_zero] using h

theorem period_from_charpoly (A : Matrix I I R) (cut period : ℕ)
    (h : A.charpoly ∣ X ^ cut * (X ^ period - 1)) :
    A ^ (cut + period) = A ^ cut := by
  obtain ⟨q, hq⟩ := h
  have hz := congrArg (aeval A) hq
  simp only [map_mul, map_pow, aeval_X, map_sub, A.aeval_self_charpoly,
    zero_mul, mul_sub, mul_one, ← pow_add] at hz
  exact sub_eq_zero.mp hz

/-- Every binary exponent at or above the cut reduces using the supplied
period. No cancellation or invertibility of the original matrix is needed. -/
theorem reduce_power (A : Matrix I I R) (cut period t : ℕ)
    (hp : A ^ (cut + period) = A ^ cut) :
    A ^ (cut + t) = A ^ (cut + t % period) := by
  have blocks (q : ℕ) : A ^ (cut + period * q) = A ^ cut := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, pow_add, ih, ← pow_add, hp]
  have split := Nat.mod_add_div t period
  calc
    A ^ (cut + t) = A ^ ((cut + period * (t / period)) + t % period) := by
      congr 1
      omega
    _ = A ^ (cut + t % period) := by rw [pow_add, blocks, ← pow_add]

end PoweredMatrixResolvent
