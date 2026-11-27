import Std

/-! Semantic kernel for critical signs and the two banks of selectors.
Assignments to the Tseitin extension gates are fixed by their inputs. -/

namespace CriticalClauseTrace

variable {State Index : Type}

theorem critical_iff_single_sign_flip (remaining literal other : State → Prop)
    (unsat : ¬∃ x, remaining x ∧ (literal x ∨ other x)) :
    (∃ x, remaining x) ↔ (∃ x, remaining x ∧ (¬literal x ∨ other x)) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx, Or.inl (fun yes => unsat ⟨x, hx, Or.inl yes⟩)⟩
  · rintro ⟨x, hx, _⟩
    exact ⟨x, hx⟩

/-- A true selector requires a deleted pin. The suffix blocks precisely
the ineligible members in the second bank. -/
def hasModel (deleteA deleteB eligible : Index → Prop) : Prop :=
  ∃ a b : Index → Prop, (∃ i, a i ∨ b i) ∧
    (∀ i, a i → deleteA i) ∧ (∀ i, b i → deleteB i) ∧
    (∀ i, b i → eligible i)

theorem model_iff (deleteA deleteB eligible : Index → Prop) :
    hasModel deleteA deleteB eligible ↔
      ∃ i, deleteA i ∨ (deleteB i ∧ eligible i) := by
  constructor
  · rintro ⟨a, b, ⟨i, root⟩, ha, hb, allowed⟩
    cases root with
    | inl x => exact ⟨i, Or.inl (ha i x)⟩
    | inr x => exact ⟨i, Or.inr ⟨hb i x, allowed i x⟩⟩
  · rintro ⟨i, found⟩
    exact ⟨deleteA, fun j => deleteB j ∧ eligible j,
      ⟨i, found⟩, fun _ h => h, fun _ h => h.1, fun _ h => h.2⟩

theorem base_unsatisfiable (eligible : Index → Prop) :
    ¬hasModel (fun _ => False) (fun _ => False) eligible := by
  simp [model_iff]

theorem every_reserve_is_critical (j : Index) (eligible : Index → Prop) :
    hasModel (fun i => i = j) (fun _ => False) eligible := by
  exact (model_iff ..).mpr ⟨j, Or.inl rfl⟩

theorem optional_critical_iff (j : Index) (eligible : Index → Prop) :
    hasModel (fun _ => False) (fun i => i = j) eligible ↔ eligible j := by
  simp [model_iff]

/-- Integer checks for the comparison of the sampling and agreement
probabilities. The one-quarter hit event costs at most two to the
minus r because 256 is two to the eighth. -/
theorem sampling_numbers :
    256 = 2^8 ∧
    64*32 < 17*127 ∧
    17^3*3^4 < 32^3*2^4 ∧
    8*256 < 191*11 ∧
    2*11^8 < 12^8 := by
  decide

end CriticalClauseTrace
