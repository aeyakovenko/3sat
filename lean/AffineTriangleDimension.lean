import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel
import AffineTriangleOracle

/-! Dimension of an affine flat on which binary inner product agrees with an
  affine answer. Checked against Lean 4.34.1 / Mathlib d13f23b7. -/

namespace AffineTriangleDimension

open Module

abbrev F := ZMod 2
abbrev Bits (n : ℕ) := Fin n → F
abbrev Inputs (n : ℕ) := Bits n × Bits n

def quad (z : Inputs n) : F := dotProduct z.1 z.2

/-- The actual polarization sends (a,b) to the functional (c,d) ↦ a·d+b·c. -/
noncomputable def polarMap (n : ℕ) : Inputs n →ₗ[F] Module.Dual F (Inputs n) where
  toFun z := ((dotProductEquiv F (Fin n) z.1).comp (LinearMap.snd _ _ _)) +
             ((dotProductEquiv F (Fin n) z.2).comp (LinearMap.fst _ _ _))
  map_add' x y := by
    apply LinearMap.ext
    intro w
    change dotProduct (x.1+y.1) w.2 + dotProduct (x.2+y.2) w.1 =
      (dotProduct x.1 w.2 + dotProduct x.2 w.1) + (dotProduct y.1 w.2 + dotProduct y.2 w.1)
    simp only [add_dotProduct]
    abel
  map_smul' t z := by
    apply LinearMap.ext
    intro w
    change dotProduct (t • z.1) w.2 + dotProduct (t • z.2) w.1 =
      t • (dotProduct z.1 w.2 + dotProduct z.2 w.1)
    simp only [smul_dotProduct, smul_add]

theorem polar_apply (z w : Inputs n) :
    polarMap n z w = dotProduct z.1 w.2 + dotProduct z.2 w.1 := rfl

theorem polar_injective (n : ℕ) : Function.Injective (polarMap n) := by
  intro x y same
  apply Prod.ext
  · apply (dotProductEquiv F (Fin n)).injective
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun same ((0 : Bits n),z)
    simpa [polar_apply] using h
  · apply (dotProductEquiv F (Fin n)).injective
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun same (z,(0 : Bits n))
    simpa [polar_apply] using h

/-- Four evaluations cancel the affine basepoint. -/
theorem polar_difference (a u v : Inputs n) :
    polarMap n u v = quad (a + (u+v)) + quad a - quad (a+u) - quad (a+v) := by
  simp only [polar_apply, quad, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm u.2 v.1]
  abel

theorem isotropic_dimension (W : Submodule F (Inputs n))
    (isotropic : ∀ u ∈ W, ∀ v ∈ W, polarMap n u v = 0) : finrank F W ≤ n := by
  let restricted : W →ₗ[F] W.dualAnnihilator :=
    (polarMap n).domRestrict W |>.codRestrict W.dualAnnihilator (fun u =>
      (Submodule.mem_dualAnnihilator _).mpr (fun v hv => isotropic u.val u.property v hv))
  have inject : Function.Injective restricted := by
    intro x y same
    apply Subtype.ext
    apply polar_injective n
    exact congrArg Subtype.val same
  have mono := LinearMap.finrank_le_finrank_of_injective inject
  have total := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have ambient : finrank F (Inputs n) = n+n := by simp [Inputs,Bits,Module.finrank_prod]
  rw [ambient] at total
  omega

theorem affine_flat_dimension (W : Submodule F (Inputs n)) (base : Inputs n)
    (output : Inputs n →ₗ[F] F) (constant : F)
    (agrees : ∀ z ∈ W, quad (base+z) = output z + constant) : finrank F W ≤ n := by
  apply isotropic_dimension W
  intro u hu v hv
  have baseval : quad base = constant := by simpa using agrees 0 W.zero_mem
  rw [polar_difference base, agrees _ (W.add_mem hu hv), baseval, agrees _ hu, agrees _ hv, map_add]
  abel

/-- Any nonempty fiber of r affine bit equations on which the quadratic
  agrees with an affine output needs at least n equations. Constants on the
  left are absorbed into the fiber value at base. -/
theorem fiber_equation_count (observations : Inputs n →ₗ[F] Bits r) (base : Inputs n)
    (output : Inputs n →ₗ[F] F) (constant : F)
    (agrees : ∀ z, observations z = observations base → quad z = output z + constant) : n ≤ r := by
  have ker_bound := affine_flat_dimension observations.ker base output (output base + constant) (by
    intro z hz
    have hz' := LinearMap.mem_ker.mp hz
    have h := agrees (base+z) (by simp [map_add,hz'])
    simpa [map_add,add_comm,add_left_comm,add_assoc] using h)
  have total := observations.finrank_range_add_finrank_ker
  have rank_bound := Submodule.finrank_le observations.range
  have ambient : finrank F (Inputs n) = n+n := by simp [Inputs,Bits,Module.finrank_prod]
  have answers : finrank F (Bits r) = r := by simp [Bits]
  rw [ambient] at total
  rw [answers] at rank_bound
  omega

structure AffineForm (n : ℕ) where
  slope : Inputs n →ₗ[F] F
  offset : F

def atom (x : Inputs n) (a : AffineForm n) : Bool := decide (a.slope x = a.offset)

/-- Complete lower bound for adaptive triangle queries on affine bit predicates,
  allowing a different affine output at each leaf of the decision tree. -/
theorem adaptive_query_count
    (tree : AffineTriangleOracle.Tree (AffineForm n) (AffineForm n))
    (correct : ∀ x : Inputs n, let form := AffineTriangleOracle.run atom x tree
                               quad x = form.slope x + form.offset) :
    n ≤ 3 * AffineTriangleOracle.depth tree := by
  obtain ⟨extra, form, count, ⟨base, baseLive⟩, sameLeaf⟩ :=
    AffineTriangleOracle.live_leaf atom tree [] ⟨0, rfl⟩
  let obs : Inputs n →ₗ[F] Bits extra.length := LinearMap.pi (fun i => (extra.get i).slope)
  have observed := fiber_equation_count obs base form.slope form.offset (by
    intro x fiber
    have live : AffineTriangleOracle.Live atom ([] ++ extra) x := by
      change extra.all (atom x) = true
      apply List.all_eq_true.mpr
      intro a ha
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
      have agrees := congrFun fiber i
      change (extra.get i).slope x = (extra.get i).slope base at agrees
      rw [hi] at agrees
      have hb := List.all_eq_true.mp (show extra.all (atom base) = true from baseLive) a ha
      simpa [atom,agrees] using hb
    have output := correct x
    simp only [sameLeaf x live] at output
    exact output)
  exact Nat.le_trans observed count

#print axioms fiber_equation_count
#print axioms adaptive_query_count

end AffineTriangleDimension
