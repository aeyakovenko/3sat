import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace MovingWalkWindows

/-- Two elementary MGG shears give a translation on every torus. -/
theorem two_shears (n : ℕ) (x y : ZMod n) :
    (x + (2 * y + 1)) - 2 * y = x + 1 ∧
    (x + 2 * y) - (2 * y + 1) = x - 1 := by
  constructor <;> ring

/-- Scalar quadratic estimate after decomposing a vector into its constant
part and its component perpendicular to constants. All energies are squared norms. -/
theorem one_window_energy
    (base perp remainder overlap density spectral : ℝ)
    (hperp : 0 ≤ perp) (hdensity : 0 ≤ density)
    (hspectral : 3 * spectral ≤ 1)
    (hshrink : remainder ≤ spectral * perp)
    (hoverlap : overlap ≤ 2 * density * base + 2 * remainder) :
    base + remainder + overlap ≤ (1 + 2 * density) * (base + perp) := by
  have h : 3 * (spectral * perp) ≤ perp := by
    nlinarith [mul_le_mul_of_nonneg_right hspectral hperp]
  nlinarith [mul_nonneg hdensity hperp]

/-- An integer exponential-moment budget selects one common walk for every
prescribed union; positive uniform weights permit repeated labels. -/
theorem some_walk_avoids_all {W F : Type} [Fintype W] [Fintype F]
    (hits : W → F → ℕ) (threshold budget : ℕ)
    (hmoment : ∀ u, ∑ w, (2 : ℕ) ^ hits w u ≤ budget)
    (hbudget : Fintype.card F * budget < Fintype.card W * (2 : ℕ) ^ threshold) :
    ∃ w, ∀ u, hits w u < threshold := by
  classical
  by_contra h
  push Not at h
  have hlower (w : W) : (2 : ℕ) ^ threshold ≤ ∑ u, (2 : ℕ) ^ hits w u := by
    obtain ⟨u, hu⟩ := h w
    calc
      (2 : ℕ) ^ threshold ≤ (2 : ℕ) ^ hits w u := Nat.pow_le_pow_right (by decide) hu
      _ ≤ ∑ u', (2 : ℕ) ^ hits w u' := Finset.single_le_sum (f := fun u' => (2 : ℕ) ^ hits w u') (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hlower w)
  have hupper := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset F)) => hmoment u)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum hupper
  rw [Finset.sum_comm] at hsum
  exact (Nat.not_lt_of_ge (hsum.trans hupper)) hbudget

/-- On a Boolean restriction, multiplying any number of neighborhood
functions depends only on the union of their active row coordinates. -/
theorem product_agrees_on_union {I R : Type} [DecidableEq I] [DecidableEq R]
    (terms : Finset I) (scope : I → Finset R)
    (f : I → (R → Bool) → ZMod 2)
    (hlocal : ∀ i ∈ terms, ∀ x y, (∀ j ∈ scope i, x j = y j) → f i x = f i y)
    (x y : R → Bool) (agree : ∀ j ∈ terms.biUnion scope, x j = y j) :
    (∏ i ∈ terms, f i x) = ∏ i ∈ terms, f i y := by
  apply Finset.prod_congr rfl
  intro i hi
  apply hlocal i hi
  intro j hj
  exact agree j (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)

#print axioms one_window_energy
#print axioms some_walk_avoids_all
#print axioms product_agrees_on_union

end MovingWalkWindows
