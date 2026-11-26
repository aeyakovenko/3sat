import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

/-! Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612, Lean 4.34.1. -/

namespace ParityQueryFiber

abbrev Bits (d : ℕ) := Fin d → ZMod 2

private def translate {d k : ℕ} (f : Bits d →ₗ[ZMod 2] Bits k) (a : Bits d) :
    LinearMap.ker f ≃ {x : Bits d // f x = f a} where
  toFun z := ⟨z.1 + a, by simp [LinearMap.mem_ker.mp z.2]⟩
  invFun z := ⟨z.1 - a, by simp [LinearMap.mem_ker, z.2]⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp

/-- A consistent answer string has exactly as many realizations as the
    kernel. A positive-dimensional kernel makes this an even cardinality;
    an inconsistent answer string has zero realizations. -/
theorem even_fiber_of_positive_kernel {d k : ℕ} (f : Bits d →ₗ[ZMod 2] Bits k)
    (positive : 0 < Module.finrank (ZMod 2) (LinearMap.ker f)) (b : Bits k) :
    Even (Fintype.card {x : Bits d // f x = b}) := by
  classical
  by_cases hit : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hit
    rw [Fintype.card_congr (translate f a).symm,
      Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
    rw [hr, pow_succ, Nat.mul_two]
    exact ⟨_, rfl⟩
  · let _ : IsEmpty {x : Bits d // f x = b} := ⟨fun x => hit ⟨x.1, x.2⟩⟩
    simp

/-- Repeated queries and linearly dependent query lists are allowed. -/
theorem even_fiber_of_fewer_queries {d k : ℕ} (f : Bits d →ₗ[ZMod 2] Bits k)
    (short : k < d) (b : Bits k) : Even (Fintype.card {x : Bits d // f x = b}) := by
  apply even_fiber_of_positive_kernel f _ b
  have rankNullity := f.finrank_range_add_finrank_ker
  have rankBound := (LinearMap.range f).finrank_le
  rw [Module.finrank_fin_fun] at rankNullity rankBound
  omega

/-- Summing a single short transcript's indicator over the binary cube
    gives the zero scalar in every characteristic-two field. -/
theorem transcript_sum_zero {d k : ℕ} (R : Type*) [Field R] [CharP R 2]
    (f : Bits d →ₗ[ZMod 2] Bits k) (short : k < d) (b : Bits k) :
    (∑ x : Bits d, if f x = b then (1 : R) else 0) = 0 := by
  rw [Finset.sum_boole, ← Fintype.card_subtype]
  exact (CharP.cast_eq_zero_iff R 2 _).mpr
    (even_iff_two_dvd.mp (even_fiber_of_fewer_queries f short b))

/-- A finite weighted sum of short transcript indicators cannot be an
    equality test for one prescribed hidden word, even with overlapping
    fibers and a different query list and field weight for every transcript. -/
theorem weighted_fibers_cannot_isolate {d : ℕ} (R : Type*) [Field R] [CharP R 2]
    {I : Type*} [Fintype I] (k : I → ℕ)
    (queries : ∀ i, Bits d →ₗ[ZMod 2] Bits (k i)) (answers : ∀ i, Bits (k i))
    (weights : I → R) (short : ∀ i, k i < d) (target : Bits d) :
    ¬ ∀ x : Bits d, (∑ i, weights i * (if queries i x = answers i then 1 else 0)) =
                 (if x = target then 1 else 0) := by
  classical
  intro realizes
  have close := Finset.sum_congr (s₁ := (Finset.univ : Finset (Bits d))) rfl
    (fun x _ => realizes x)
  rw [Finset.sum_comm] at close
  have inner (i : I) :
      (∑ x : Bits d, weights i * (if queries i x = answers i then 1 else 0)) = 0 := by
    rw [← Finset.mul_sum, transcript_sum_zero R _ (short i) _, mul_zero]
  rw [Finset.sum_eq_zero (fun i _ => inner i)] at close
  simp at close

end ParityQueryFiber
