import Std

/-! Semantics of the finite proper ternary clause gadgets in packed_residue_dimacs.py.
A true flag at k means the state has residue k in F₃. -/
namespace PackedResidueAdder

def increment (old record : Fin 3) (flags : Fin 3 → Bool) : Prop :=
  (∀ i j : Fin 3, old = i → record = j → flags (i+j) = true) ∧
  (∀ i j : Fin 3, i ≠ j → ¬(flags i = true ∧ flags j = true))

theorem one_hot (old record : Fin 3) (flags : Fin 3 → Bool) :
    increment old record flags ↔ ∀ i, flags i = decide (i = old+record) := by
  constructor
  · intro ⟨active, unique⟩ i
    have on := active old record rfl rfl
    by_cases h : i = old+record
    · simpa [h] using on
    · simp [h]
      cases hb : flags i
      · rfl
      · exact False.elim (unique i (old+record) h ⟨hb,on⟩)
  · intro h
    constructor
    · intro i j hi hj
      subst i
      subst j
      simp [h]
    · intro i j distinct pair
      have h1 : i = old+record := of_decide_eq_true ((h i).symm.trans pair.1)
      have h2 : j = old+record := of_decide_eq_true ((h j).symm.trans pair.2)
      exact distinct (h1.trans h2.symm)

/-- A payload triple with its pass flag splits into two proper ternary clauses. -/
theorem gated : ∀ a b c pass : Bool,
    (∃ bridge : Bool, (a || b || bridge) = true ∧ (!bridge || c || pass) = true) ↔
    (a || b || c || pass) = true := by decide

/-- The seven clauses generated over the pad triangle exclude the seven
nonzero assignments and force all three padding bits to false. -/
theorem pads : ∀ a b c : Bool,
  ((!a || b || c) && (a || !b || c) && (!a || !b || c) &&
    (a || b || !c) && (!a || b || !c) && (a || !b || !c) && (!a || !b || !c)) = true ↔
    a = false ∧ b = false ∧ c = false := by decide

end PackedResidueAdder
