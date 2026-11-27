import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Interpolation at the addresses actually used and the row-support bound
for the two-tag decoder. These lemmas do not assume the cells form an interval. -/

namespace QueriedCutMemory

open Finset Polynomial Submodule

variable {F X Y : Type*} [Field F]

/-- Each data row can use a different set of genuine old addresses.
A polynomial for that row is exact at every required address. -/
theorem polynomial_on_reads (keys : X → Finset F) (contents : X → F → F) :
    ∃ p : X → F[X], (∀ x, (p x).degree < ((keys x).card : WithBot ℕ)) ∧
      ∀ x, ∀ a ∈ keys x, (p x).eval a = contents x a := by
  classical
  refine ⟨fun x => Lagrange.interpolate (keys x) id (contents x), ?_, ?_⟩
  · intro x
    exact Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
  · intro x a ha
    exact Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) ha

/-- Evaluation at a known address is linear even over a subfield. In the RAM
application the subfield is the two-element field. -/
def evalAt {K : Type*} [Field K] [Algebra K F] (a : F) : F[X] →ₗ[K] F where
  toFun p := p.eval a
  map_add' := by intro p q; exact Polynomial.eval_add
  map_smul' := by intro c p; simp

/-- No nonzero column can be absent from all rows of a row basis. -/
theorem columns_le_row_support [Fintype X] [Fintype Y] [DecidableEq F]
    (A : Matrix X Y F) (h : ℕ)
    (covered : ∀ y, ∃ x, A x y ≠ 0)
    (row_bound : ∀ x, (univ.filter (fun y => A x y ≠ 0)).card ≤ h) :
    Fintype.card Y ≤ A.rank * h := by
  classical
  obtain ⟨basisRows, actual, num, spans, _⟩ :=
    exists_finset_span_eq_linearIndepOn F (Set.range A.row)
  let support := fun r : Y → F => univ.filter (fun y => r y ≠ 0)
  have cover : univ ⊆ basisRows.biUnion support := by
    intro y _
    by_contra absent
    have vanish : ∀ r ∈ basisRows, r y = 0 := by
      intro r hr
      by_contra hn
      exact absent (mem_biUnion.mpr ⟨r, hr, mem_filter.mpr ⟨mem_univ _, hn⟩⟩)
    let atY := LinearMap.proj (R := F) (φ := fun _ : Y => F) y
    have sub : span F (↑basisRows : Set (Y → F)) ≤ LinearMap.ker atY := by
      apply span_le.mpr
      intro r hr
      exact vanish r hr
    obtain ⟨x, hx⟩ := covered y
    have mem : A.row x ∈ span F (Set.range A.row) :=
      subset_span ⟨x, rfl⟩
    rw [← spans] at mem
    exact hx (sub mem)
  calc
    Fintype.card Y = (univ : Finset Y).card := rfl
    _ ≤ (basisRows.biUnion support).card := card_le_card cover
    _ ≤ ∑ r ∈ basisRows, (support r).card := card_biUnion_le
    _ ≤ ∑ _r ∈ basisRows, h := by
      apply sum_le_sum
      intro r hr
      obtain ⟨x, rfl⟩ := actual hr
      exact row_bound x
    _ = A.rank * h := by simp [num, Matrix.rank_eq_finrank_span_row]

/-- A parity-check map certifies every nonzero error in the promised set.
Syndrome equality on a non-error input is allowed to require a fallback. -/
theorem syndrome_detects {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F V] [Module F W] (H : V →ₗ[F] W) (errors : Set V)
    (separates : ∀ z ∈ errors, H z = 0 → z = 0)
    {x y : V} (small : x - y ∈ errors) :
    H x = H y ↔ x = y := by
  constructor
  · intro eqSyndrome
    apply sub_eq_zero.mp
    apply separates _ small
    rw [map_sub, eqSyndrome, sub_self]
  · rintro rfl
    rfl

#print axioms syndrome_detects
#print axioms polynomial_on_reads
#print axioms columns_le_row_support

end QueriedCutMemory
