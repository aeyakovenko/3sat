import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! Two finite facts about implicit batches of balanced three-bit selectors. -/

namespace BalancedSelectorCut

/-- One odd parity row and three implications recognize a three-literal clause. -/
theorem odd_markers (a b c : Bool) :
    (a || b || c) = true ↔
    ∃ x y z : Bool, ((x ^^ y) ^^ z) = true ∧
      (x = true → a = true) ∧ (y = true → b = true) ∧ (z = true → c = true) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Every distinct residual membership table needs a different forward state. -/
theorem cut_states {Selector State : Type} [Fintype Selector] [Fintype State]
    (encode : (Selector → Bool) → State) (suffix : State → Selector → Bool)
    (correct : ∀ table x, suffix (encode table) x = table x) :
    2 ^ Fintype.card Selector ≤ Fintype.card State := by
  classical
  have inj : Function.Injective encode := by
    intro f g equal
    funext x
    rw [← correct f x, equal, correct g x]
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective encode inj

theorem boolean_cut_states {p : Nat} {State : Type} [Fintype State]
    (encode : ((Fin p → Bool) → Bool) → State) (suffix : State → (Fin p → Bool) → Bool)
    (correct : ∀ table x, suffix (encode table) x = table x) :
    2 ^ 2 ^ p ≤ Fintype.card State := by
  simpa [Fintype.card_fun] using cut_states encode suffix correct

/-- The constant-free terminal pin has one complete assignment. -/
theorem false_pin (f a b c d : Bool) :
    (b = (f && a) ∧ d = (a && c) ∧ d = !(b && c)) ↔
      f = false ∧ a = true ∧ b = false ∧ c = true ∧ d = true := by
  cases f <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- A directed cycle of nondecreasing state bits is constant. -/
theorem monotone_cycle {t : Nat → Bool} {i length : Nat} (h : Monotone t)
    (closes : t length = t 0) (before : i ≤ length) : t i = t 0 := by
  apply le_antisymm
  · rw [← closes]
    exact h before
  · exact h (Nat.zero_le i)

#print axioms false_pin
#print axioms monotone_cycle
#print axioms odd_markers
#print axioms boolean_cut_states

end BalancedSelectorCut
