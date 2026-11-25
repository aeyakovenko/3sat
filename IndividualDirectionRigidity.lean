import Std

namespace IndividualDirectionRigidity

/-- After testing each coordinate direction, f i reads only column i.
Testing e_i + e_j gives this identity by moving y into column i. -/
def PairConsistency {I X : Type} (add : X → X → X) (zero : X)
    (f : I → X → Bool) : Prop :=
  ∀ i j, i ≠ j → ∀ x y, f i x ^^ f j y = f i (add x y) ^^ f j zero

/-- Exact extraction of a shared additive linear form from individual column
responses. Applying this one output bit at a time recovers the left matrix. -/
theorem extract {I X : Type} (add : X → X → X) (zero : X)
    (zero_add : ∀ x, add zero x = x)
    (f : I → X → Bool) (consistent : PairConsistency add zero f)
    (i₀ i₁ : I) (distinct : i₀ ≠ i₁) :
    ∃ L : X → Bool,
      (∀ x y, L (add x y) = (L x ^^ L y)) ∧
      (∀ i x, f i x = (f i zero ^^ L x)) := by
  let L := fun x => f i₀ x ^^ f i₀ zero
  have shared (i : I) (x : X) : f i x = (f i zero ^^ L x) := by
    by_cases eq : i = i₀
    · subst i
      simp only [L]
      bv_decide
    · have h := consistent i₀ i (Ne.symm eq) zero x
      rw [zero_add] at h
      simp only [L]
      bv_decide
  refine ⟨L, ?_, shared⟩
  intro x y
  have h := consistent i₀ i₁ distinct x y
  have h' := shared i₁ y
  simp only [L] at *
  bv_decide

end IndividualDirectionRigidity
