import Std

namespace SplitUnitBatchRank

variable {Block Position Symbol : Type}

/-- Semantics of the two private guarded unit clauses at each position. -/
def enabledUnits (z : Block → Prop) (a b : Block → Position → Symbol)
    (cell : Block → Position → Symbol → Prop) : Prop :=
  ∀ i j, z i → cell i j (a i j) ∧ ¬ cell i j (b i j)

/-- An inactive block selects a position. Both private sides mark its symbol
in a shared bank whose public clauses allow at most one marked symbol. -/
def disabledCollision (z : Block → Prop) (a b : Block → Position → Symbol)
    (pick : Block → Position → Prop) (mark : Block → Symbol → Prop) : Prop :=
  (∀ i, ¬ z i → ∃ j, pick i j) ∧
  (∀ i j, pick i j → mark i (a i j) ∧ mark i (b i j)) ∧
  (∀ i u v, mark i u → mark i v → u = v)

/-- For any finite circuit predicate h, the encoded output is forced to be the
actual aggregate. The statement of semantic correctness also works on infinite
index types. -/
theorem aggregate_exact (a b : Block → Position → Symbol) (h : (Block → Prop) → Prop) :
    (∃ z cell pick mark, h z ∧ enabledUnits z a b cell ∧
      disabledCollision z a b pick mark) ↔ h (fun i => ∀ j, a i j ≠ b i j) := by
  classical
  constructor
  · rintro ⟨z, cell, pick, mark, hz, hu, hw, hm, hsingle⟩
    have heq : z = fun i => ∀ j, a i j ≠ b i j := by
      funext i
      apply propext
      constructor
      · intro hi j hsame
        obtain ⟨ha, hb⟩ := hu i j hi
        exact hb (hsame ▸ ha)
      · intro hall
        apply Classical.byContradiction
        intro hno
        obtain ⟨j, hj⟩ := hw i hno
        obtain ⟨ha, hb⟩ := hm i j hj
        exact hall j (hsingle i _ _ ha hb)
    exact heq ▸ hz
  · intro hz
    let z := fun i => ∀ j, a i j ≠ b i j
    have witness : ∀ i, ¬z i → ∃ j, a i j = b i j := by
      intro i hi
      apply Classical.byContradiction
      intro hnone
      exact hi (fun j heq => hnone ⟨j, heq⟩)
    let chosen := fun i (hi : ¬z i) => Classical.choose (witness i hi)
    let pick := fun i j => ∃ hi : ¬z i, j = chosen i hi
    let mark := fun i u => ∃ hi : ¬z i, u = a i (chosen i hi)
    refine ⟨z, fun i j u => u = a i j, pick, mark, hz, ?_, ?_, ?_, ?_⟩
    · intro i j hi
      exact ⟨rfl, fun heq => hi j heq.symm⟩
    · exact fun i hi => ⟨chosen i hi, hi, rfl⟩
    · rintro i j ⟨hi, rfl⟩
      exact ⟨⟨hi, rfl⟩, ⟨hi, (Classical.choose_spec (witness i hi)).symm⟩⟩
    · rintro i u v ⟨hi, rfl⟩ ⟨_, rfl⟩
      rfl

end SplitUnitBatchRank
