import Std

namespace PhaseOrderedZeroReads

/-- The two ordinal tests are exactly a digit inequality. -/
theorem digit_order (B a b : Nat) (ha : a < B) (hb : b < B) :
    (a < b ∨ B - 1 - a < B - 1 - b) ↔ a ≠ b := by
  omega

/-- The checker observes no flag exactly when the entire digit arrays agree. -/
theorem all_tests_clean {I : Type} (B : Nat) (left right : I → Nat)
    (leftBound : ∀ i, left i < B) (rightBound : ∀ i, right i < B) :
    (∀ i, ¬(left i < right i ∨ B - 1 - left i < B - 1 - right i)) ↔
    left = right := by
  constructor
  · intro h
    funext i
    have no : ¬left i ≠ right i := fun ne =>
      h i ((digit_order _ _ _ (leftBound i) (rightBound i)).2 ne)
    omega
  · rintro rfl i
    simp

/-- Write events here are all preceding the load, including earlier slots in
the load phase. A local check bounds own writes; an interval certificate
bounds the opposite writes. Thus the candidate bounds the genuine history. -/
theorem latest_phase {W : Nat → Prop} {color : Nat → Bool} {i j : Nat}
    (beforeLoad : ∀ p, W p → p ≤ j)
    (own : ∀ p, W p → color p = color j → p ≤ i)
    (exclusion : ∀ p, i < p → p < j → color p ≠ color j → ¬W p) :
    ∀ p, W p → p ≤ i := by
  intro p hp
  by_cases hcolor : color p = color j
  · exact own p hp hcolor
  · have hne : p ≠ j := fun h => hcolor (congrArg color h)
    have hlt : p < j := by have := beforeLoad p hp; omega
    have notLater : ¬i < p := fun later => exclusion p later hlt hcolor hp
    omega

/-- A common public node of an interval cover and point's ancestor path
exists precisely on interval membership, for any exact cover. -/
theorem interval_key {Phase Node : Type} (inside : Phase → Prop)
    (used : Node → Prop) (beneath : Phase → Node → Prop)
    (exactCover : ∀ p, inside p ↔ ∃ v, used v ∧ beneath p v)
    (writes : Phase → Prop) :
    (∃ p, writes p ∧ inside p) ↔ ∃ v, used v ∧ ∃ p, writes p ∧ beneath p v := by
  constructor
  · rintro ⟨p, hp, insideP⟩
    obtain ⟨v, hv, edge⟩ := (exactCover p).1 insideP
    exact ⟨v, hv, p, hp, edge⟩
  · rintro ⟨v, hv, p, hp, edge⟩
    exact ⟨p, hp, (exactCover p).2 ⟨v, hv, edge⟩⟩

end PhaseOrderedZeroReads
