import Std

namespace CalibratedCylinderSeparation

variable {Input Prefix : Type}

def Covers (length : Input → Nat) (appendPrefix : Prefix → Input → Input)
    (diagonal value : Input → Bool) : Prop :=
  ∀ p N, ∃ y, N ≤ length y ∧ value (appendPrefix p y) = diagonal (appendPrefix p y)

private theorem eq_flip_of_ne (a b : Bool) (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

/-- The hypotheses isolate the machine constructions from the length and sign quantifiers. -/
theorem coverage_iff_separation
    (length : Input → Nat) (appendPrefix : Prefix → Input → Input) (diagonal : Input → Bool)
    (high low : (Input → Bool) → Prop)
    (selfPrefix : ∀ f, low f → ∃ p N, ∀ y, N ≤ length y →
      diagonal (appendPrefix p y) = !(f (appendPrefix p y)))
    (saturated : ∀ p, low (fun y => !(diagonal (appendPrefix p y))))
    (finiteCorrections : ∀ f g N, low g → (∀ y, N ≤ length y → f y = g y) → low f)
    (onSuffix : ∀ f, high f → ∃ v, high v ∧ ∀ p y, v (appendPrefix p y) = f y) :
    (∃ v, high v ∧ Covers length appendPrefix diagonal v) ↔
      ∃ h, high h ∧ ¬low h := by
  constructor
  · rintro ⟨v, hv, hc⟩
    refine ⟨v, hv, ?_⟩
    intro hl
    obtain ⟨p, N, hflip⟩ := selfPrefix v hl
    obtain ⟨y, hy, hgood⟩ := hc p N
    have hfalse := hgood.trans (hflip y hy)
    cases h : v (appendPrefix p y) <;> simp [h] at hfalse
  · rintro ⟨h, hh, hout⟩
    obtain ⟨v, hv, heval⟩ := onSuffix h hh
    refine ⟨v, hv, ?_⟩
    intro p N
    apply Classical.byContradiction
    intro hnone
    apply hout
    apply finiteCorrections h (fun y => !(diagonal (appendPrefix p y))) N (saturated p)
    intro y hy
    apply eq_flip_of_ne
    intro heq
    exact hnone ⟨y, hy, (heval p y).trans heq⟩

end CalibratedCylinderSeparation
