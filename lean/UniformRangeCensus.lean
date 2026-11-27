import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! Counting the joint image of a finite census of stretching maps. -/

namespace UniformRangeCensus

/-- The competitors may have overlapping images. Their total number of inputs
    still bounds the joint image, independent of how the maps were obtained. -/
theorem common_omission {J D R : Type*} [Fintype J] [Fintype D] [Fintype R]
    (eval : J → D → R)
    (small : Fintype.card J * Fintype.card D < Fintype.card R) :
    ∃ z : R, ∀ j : J, ∀ d : D, eval j d ≠ z := by
  classical
  by_contra! covers
  let map : J × D → R := fun p => eval p.1 p.2
  have onto : Function.Surjective map := by
    intro z
    obtain ⟨j, d, found⟩ := covers z
    exact ⟨(j, d), found⟩
  have lower := Fintype.card_le_of_surjective map onto
  rw [Fintype.card_prod] at lower
  exact (Nat.not_le_of_lt small) lower

abbrev Bits (n : Nat) := Fin n → Bool

def takeBits {r m : Nat} (h : r ≤ m) (x : Bits m) : Bits r :=
  fun i => x (i.castLE h)

def zeroExtend {r m : Nat} (v : Bits r) : Bits m :=
  fun i => if hi : i.val < r then v ⟨i.val,hi⟩ else false

theorem prefix_zeroExtend {r m : Nat} (h : r ≤ m) (v : Bits r) :
    takeBits h (zeroExtend v) = v := by
  funext i
  simp [takeBits, zeroExtend]

/-- A jointly omitted prefix is enough. Every extension, including padding
    the prefix by zeros, is outside every full range. -/
theorem missing_prefix {j ℓ r m : Nat} (h : r ≤ m)
    (eval : Fin j → Bits ℓ → Bits m) (small : j * 2 ^ ℓ < 2 ^ r) :
    ∃ v : Bits r, (∀ i y, takeBits h (eval i y) ≠ v) ∧
      (∀ z : Bits m, takeBits h z = v → ∀ i y, eval i y ≠ z) := by
  have sizes : Fintype.card (Fin j) * Fintype.card (Bits ℓ) < Fintype.card (Bits r) := by
    simpa [Bits] using small
  obtain ⟨v, omitted⟩ := common_omission (fun i y => takeBits h (eval i y)) sizes
  refine ⟨v, omitted, ?_⟩
  intro z hv i y he
  exact omitted i y ((congrArg (takeBits h) he).trans hv)

theorem missing_zero_extension {j ℓ r m : Nat} (h : r ≤ m)
    (eval : Fin j → Bits ℓ → Bits m) (small : j * 2 ^ ℓ < 2 ^ r) :
    ∃ v : Bits r, ∀ i y, eval i y ≠ (zeroExtend v : Bits m) := by
  obtain ⟨v, _, allExtensions⟩ := missing_prefix h eval small
  exact ⟨v, allExtensions (zeroExtend v) (prefix_zeroExtend h v)⟩

/-- Two one-element ranges already distinguish a hole for each family from
    a single hole for all families, when the small-census bound is absent. -/
theorem individual_versus_common :
    let eval : Bool → Unit → Bool := fun family _ => family
    (∀ family, ∃ z, ∀ y, eval family y ≠ z) ∧
    (∀ z, ∃ family y, eval family y = z) := by
  constructor
  · intro family
    cases family
    · exact ⟨true, fun _ => by change false ≠ true; decide⟩
    · exact ⟨false, fun _ => by change true ≠ false; decide⟩
  · intro z
    exact ⟨z, (), rfl⟩

/-- At a single length, hitting every possible output table once is equivalent
    to covering all output values at one fixed index. The equivalence also
    holds for arbitrary types when the adversary may be any function. -/
theorem single_hit_iff_covered {X Y J D : Type*} (eval : J → X → D → Y) :
    (∀ a : X → Y, ∃ x i d, eval i x d = a x) ↔
      ∃ x, ∀ y, ∃ i d, eval i x d = y := by
  classical
  constructor
  · intro hits
    by_contra! omitted
    choose a avoids using omitted
    obtain ⟨x, i, d, hit⟩ := hits a
    exact avoids x i d hit
  · rintro ⟨x, covers⟩ a
    obtain ⟨i, d, hit⟩ := covers (a x)
    exact ⟨x, i, d, hit⟩

/-- A single-hit census must pay for the full range even when it can
    choose the index of the hit separately for each proposed table. -/
theorem single_hit_size {X Y J D : Type*} [Fintype Y] [Fintype J] [Fintype D]
    (eval : J → X → D → Y) (hits : ∀ a : X → Y, ∃ x i d, eval i x d = a x) :
    Fintype.card Y ≤ Fintype.card J * Fintype.card D := by
  obtain ⟨x, covers⟩ := (single_hit_iff_covered eval).mp hits
  let atIndex : J × D → Y := fun p => eval p.1 x p.2
  have onto : Function.Surjective atIndex := by
    intro y
    obtain ⟨i, d, hit⟩ := covers y
    exact ⟨(i,d), hit⟩
  simpa using Fintype.card_le_of_surjective atIndex onto

/-- An output with a header of h bits and payload of ℓ bits admits an
    optimal family: fix its header, and use the seed verbatim as its tail. -/
theorem matching_census {X : Type*} (x₀ : X) (h ℓ : Nat) :
    ∃ eval : Bits h → X → Bits ℓ → Bits (h + ℓ),
      (∀ a : X → Bits (h + ℓ), ∃ x i d, eval i x d = a x) ∧
      Fintype.card (Bits h) * Fintype.card (Bits ℓ) = Fintype.card (Bits (h + ℓ)) := by
  refine ⟨fun i _ d => Fin.addCases i d, ?_, ?_⟩
  · apply (single_hit_iff_covered _).mpr
    refine ⟨x₀, ?_⟩
    intro y
    refine ⟨fun j => y (Fin.castAdd ℓ j), fun j => y (Fin.natAdd h j), ?_⟩
    funext j
    exact Fin.addCases (fun i => by simp) (fun k => by simp) j
  · simp [Bits, pow_add]

#print axioms single_hit_iff_covered
#print axioms single_hit_size
#print axioms matching_census
#print axioms common_omission
#print axioms missing_zero_extension
#print axioms individual_versus_common

end UniformRangeCensus
