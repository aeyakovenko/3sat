import AffineTriangleDimension
import OneAdditionParity
import Mathlib.Tactic.FinCases

/-! Bound on the number of independent inner-product pairs computed by a single
modular addition with affine input bits, an arbitrary output mask and an affine
direct contribution. The operands and mask all have width `w`, also for `w=0`.
List rows are ordered from most to least significant. -/
namespace OneAdditionInnerProduct

open AffineTriangleDimension
open OneAdditionParity (Row obeys sumParity)

/-- Convert the two field elements to Boolean bits. -/
def bit (x : F) : Bool := decide (x = 1)

private theorem bit_add (x y : F) : bit (x+y) = (bit x ^^ bit y) := by
  fin_cases x <;> fin_cases y <;> decide

private theorem bit_injective : Function.Injective bit := by
  intro x y h
  fin_cases x <;> fin_cases y <;> first | rfl | contradiction

/-- Boolean bit of an actual affine form on the two input vectors. -/
def eval (a : AffineForm m) (z : Inputs m) := bit (a.slope z + a.offset)

private def represented (f : Inputs m → Bool) : Prop := ∃ a : AffineForm m, f = eval a

private theorem zero_represented : represented (m := m) (fun _ => false) := by
  exact ⟨⟨0,0⟩, by funext z; rfl⟩

private theorem xor_represented (f g : Inputs m → Bool) (hf : represented f) (hg : represented g) :
    represented (fun z => f z ^^ g z) := by
  obtain ⟨a,rfl⟩ := hf
  obtain ⟨b,rfl⟩ := hg
  refine ⟨⟨a.slope + b.slope, a.offset + b.offset⟩, ?_⟩
  funext z
  change (bit (a.slope z + a.offset) ^^ bit (b.slope z + b.offset)) =
    bit ((a.slope z + b.slope z) + (a.offset + b.offset))
  rw [← bit_add]
  congr 1
  abel

private theorem obeys_iff {E : Type} (cs : List ((E → Bool) × Bool)) (x : E) :
    obeys cs x ↔ ∀ p ∈ cs, p.1 x = p.2 := by
  induction cs with
  | nil => simp [obeys]
  | cons p cs ih => cases p; simp [obeys,ih]

/-- A mask bit and both affine operand bits share the same index at each
position. This construction fixes the width independently of the mask weight. -/
def rows (mask : Fin w → Bool) (left right : Fin w → AffineForm m) : List (Row (Inputs m)) :=
  List.ofFn (fun i => ⟨mask i, eval (left i), eval (right i)⟩)

/-- For any two affine-encoded `w`-bit operands, any `w`-bit output mask, and
any affine offset, exact computation of the inner product forces `2*m ≤ w`,
expressed equivalently as `m ≤ w/2`. -/
theorem width_bound (mask : Fin w → Bool) (left right : Fin w → AffineForm m)
    (offset : AffineForm m)
    (correct : ∀ z : Inputs m,
      (eval offset z ^^ sumParity (rows mask left right) z) = bit (quad z)) :
    m ≤ w / 2 := by
  classical
  let rs := rows mask left right
  have valid : ∀ a ∈ rs, represented a.x ∧ represented a.y := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨⟨left i, rfl⟩, ⟨right i, rfl⟩⟩
  obtain ⟨cs, f, cost, hc, ⟨out,hout⟩, ⟨base, _, hbase⟩, hflat⟩ :=
    OneAdditionParity.live_word_parity represented zero_represented xor_represented
      (fun _ => True) ⟨0,True.intro⟩ rs valid (eval offset) ⟨offset,rfl⟩
  have forms (i : Fin cs.length) : ∃ a : AffineForm m, (cs.get i).1 = eval a :=
    hc (cs.get i) (cs.get_mem i)
  choose coeff coeff_spec using forms
  let obs : Inputs m →ₗ[F] Bits cs.length := LinearMap.pi (fun i => (coeff i).slope)
  have rank := fiber_equation_count obs base out.slope out.offset (by
    intro z hz
    have hz_live : obeys cs z := by
      apply (obeys_iff cs z).mpr
      intro p hp
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
      have same : (coeff i).slope z = (coeff i).slope base := congrFun hz i
      have good := (obeys_iff cs base).mp hbase (cs.get i) (cs.get_mem i)
      rw [coeff_spec i] at good ⊢
      simpa only [eval,same] using good
    apply bit_injective
    calc bit (quad z) = (eval offset z ^^ sumParity rs z) := (correct z).symm
         _ = f z := hflat z True.intro hz_live
         _ = bit (out.slope z + out.offset) := by rw [hout]; rfl)
  exact rank.trans (by simpa [rs,rows] using cost)

#print axioms width_bound

end OneAdditionInnerProduct
