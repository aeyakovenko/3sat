import Std

namespace SignedUnaryInterval

/-- An interior copying a sound negative verifier cannot be positive. -/
theorem copied_negative (source quick : Prop) (copy : source ↔ quick)
    (sound : quick → ¬source) : ¬source ∧ ¬quick := by
  have no : ¬source := fun hs => sound (copy.mp hs) hs
  exact ⟨no, fun hq => no (copy.mpr hq)⟩

theorem alternate_even (u : Nat → Bool) (k : Nat)
    (step : ∀ i, i < 2*k → u (i+1) = !(u i)) : u (2*k) = u 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have prev := ih (by intro i hi; exact step i (by omega))
    have h₀ := step (2*k) (by omega)
    have h₁ := step (2*k+1) (by omega)
    rw [show 2*(k+1) = (2*k+1)+1 by omega, h₁, h₀, Bool.not_not, prev]

/-- An even-cardinality interval also defeats the unshifted complementary candidate. -/
theorem no_complement_on_odd_gap (u h : Nat → Bool) (k : Nat)
    (interior : ∀ i, i < 2*k+1 → h i = u (i+1))
    (close : h (2*k+1) = !(u 0))
    (opposite : ∀ i, i ≤ 2*k+1 → h i = !(u i)) : False := by
  have step : ∀ i, i < 2*k+1 → u (i+1) = !(u i) := by
    intro i hi
    exact (interior i hi).symm.trans (opposite i (by omega))
  have even := alternate_even u k (by intro i hi; exact step i (by omega))
  have last := step (2*k) (by omega)
  have clash := close.symm.trans (opposite (2*k+1) (by omega))
  rw [last, even, Bool.not_not] at clash
  cases hu : u 0 <;> simp [hu] at clash

def Incl {ι : Type} (p q : ι → Prop) : Prop := ∀ i, p i → q i

theorem monotone_fixed_point {ι : Type} (F : (ι → Prop) → ι → Prop)
    (increasing : ∀ {p q}, Incl p q → Incl (F p) (F q)) :
    ∃ x, ∀ i, x i ↔ F x i := by
  let x : ι → Prop := fun i => ∀ z, Incl (F z) z → z i
  have prefixed : Incl (F x) x := by
    intro i hi z hz
    have below : Incl x z := fun j hj => hj z hz
    exact hz i (increasing below i hi)
  have postfixed : Incl x (F x) := by
    intro i hi
    exact hi (F x) (increasing prefixed)
  exact ⟨x, fun i => ⟨postfixed i, prefixed i⟩⟩

/-- Positive tests of two nested predicates always have a Boolean-difference
realization, even with a specified set of negated output equations. -/
theorem signed_positive_difference {ι : Type} (endpoints : ι → Prop)
    (G : (ι → Prop) → (ι → Prop) → ι → Prop)
    (increasing : ∀ {p q p' q'}, Incl p p' → Incl q q' → Incl (G p q) (G p' q')) :
    ∃ p q, Incl q p ∧ ∀ i, (p i ∧ ¬q i) ↔
      ((endpoints i → ¬G p q i) ∧ (¬endpoints i → G p q i)) := by
  classical
  let p (x : ι → Prop) (i : ι) := endpoints i ∨ x i
  let q (x : ι → Prop) (i : ι) := endpoints i ∧ x i
  let F (x : ι → Prop) := G (p x) (q x)
  have hF : ∀ {x y}, Incl x y → Incl (F x) (F y) := by
    intro x y h
    apply increasing
    · intro i hi
      exact hi.imp id (h i)
    · intro i hi
      exact ⟨hi.1, h i hi.2⟩
  obtain ⟨x, hx⟩ := monotone_fixed_point F hF
  refine ⟨p x, q x, fun i hi => Or.inl hi.1, ?_⟩
  intro i
  have hi : x i ↔ G (p x) (q x) i := hx i
  by_cases he : endpoints i
  · simp [p, q, he] at hi ⊢
    exact not_congr hi
  · simp [p, q, he] at hi ⊢
    exact hi

end SignedUnaryInterval
