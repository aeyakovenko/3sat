import Std

namespace MatchingCoordinatePermanent

/-- The four private vertices of a subdivided edge meet precisely one chosen
edge each. The middle and the two outside edges have the same status. -/
theorem path_modes (a b c d e : Bool) (ab : a ≠ b) (bc : b ≠ c)
    (cd : c ≠ d) (de : d ≠ e) :
    a = c ∧ c = e ∧ b = !c ∧ d = !c := by
  revert a b c d e
  decide

/-- Endpoint constraints become exactly the row and column matching
constraints on the prescribed central entries. -/
theorem middle_matching {I J : Type}
    (left p middle q right : I → J → Bool)
    (internal : ∀ i j, left i j ≠ p i j ∧ p i j ≠ middle i j ∧
                       middle i j ≠ q i j ∧ q i j ≠ right i j)
    (leftMatch : ∀ i, ∃ j, ∀ j', left i j' = true ↔ j' = j)
    (rightMatch : ∀ j, ∃ i, ∀ i', right i' j = true ↔ i' = i) :
    (∀ i, ∃ j, ∀ j', middle i j' = true ↔ j' = j) ∧
    (∀ j, ∃ i, ∀ i', middle i' j = true ↔ i' = i) := by
  have mode := fun i j =>
    path_modes _ _ _ _ _ (internal i j).1 (internal i j).2.1
      (internal i j).2.2.1 (internal i j).2.2.2
  constructor
  · intro i
    obtain ⟨j, h⟩ := leftMatch i
    exact ⟨j, fun j' => (mode i j').1 ▸ h j'⟩
  · intro j
    obtain ⟨i, h⟩ := rightMatch j
    exact ⟨i, fun i' => (mode i' j).2.1.symm ▸ h i'⟩

/-- Each base edge choice has a unique completion on its private path. -/
theorem unique_extension (c : Bool) :
    (c ≠ !c ∧ (!c) ≠ c ∧ c ≠ !c ∧ (!c) ≠ c) ∧
    ∀ a b d e : Bool, a ≠ b → b ≠ c → c ≠ d → d ≠ e →
      a = c ∧ b = !c ∧ d = !c ∧ e = c := by
  constructor
  · cases c <;> decide
  · intro a b d e h₁ h₂ h₃ h₄
    obtain ⟨ha, he, hb, hd⟩ := path_modes a b c d e h₁ h₂ h₃ h₄
    exact ⟨ha, hb, hd, he.symm⟩

end MatchingCoordinatePermanent
