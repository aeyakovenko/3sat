import Std

namespace ForcingLayouts

/-- Occurrence identifiers need not map injectively to claims. Every
occurrence has checked prerequisites of smaller rank. -/
theorem supportedSound {Occurrence Claim : Type}
    (conclusion : Occurrence → Claim) (valid : Claim → Prop)
    (rank : Occurrence → Nat) (uses : Occurrence → Occurrence → Prop)
    (decreases : ∀ i j, uses i j → rank j < rank i)
    (ruleSound : ∀ i, (∀ j, uses i j → valid (conclusion j)) → valid (conclusion i))
    (root : Occurrence) : valid (conclusion root) := by
  have byRank : ∀ r i, rank i = r → valid (conclusion i) := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r smaller =>
      intro i hi
      apply ruleSound i
      intro j hj
      exact smaller (rank j) (hi ▸ decreases i j hj) j rfl
  exact byRank (rank root) root rfl

/-- Choosing ports of an AND gate is a valid certificate when every
completion of the chosen inputs gives the asserted result. -/
def forcesAnd (keepLeft keepRight left right out : Bool) : Prop :=
  ∀ a b : Bool, (keepLeft = true → a = left) →
    (keepRight = true → b = right) → (a && b) = out

theorem trueAndNeedsBoth (k l a b : Bool) :
    forcesAnd k l a b true ↔ k = true ∧ l = true ∧ a = true ∧ b = true := by
  unfold forcesAnd
  cases k <;> cases l <;> cases a <;> cases b <;> decide

theorem falseAndLeft (right : Bool) : forcesAnd true false false right false := by
  intro a b ha _
  simp [ha rfl]

/-- A common bag can be provided to each check by bringing its (at most
two) prerequisites into every bag containing the conclusion. -/
theorem expandedBagLength {α : Type} (bag : List α) (parents : α → List α)
    (binary : ∀ x, (parents x).length ≤ 2) :
    (bag.flatMap (fun x => x :: parents x)).length ≤ 3 * bag.length := by
  induction bag with
  | nil => simp
  | cons x xs ih =>
    have bound := binary x
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

end ForcingLayouts
