import Std

namespace ClauseSelectorLift

/-- XOR over all k-bit lists of the value of a Boolean function. -/
def parity : Nat → (List Bool → Bool) → Bool
  | 0, f => f []
  | k + 1, f =>
    xor (parity k (fun xs => f (false :: xs))) (parity k (fun xs => f (true :: xs)))

/-- Two independently optional copies of one clause enable that clause iff
    at least one copy is present. -/
def duplicate (f : List Bool → Bool) : List Bool → Bool
  | a :: b :: rest => f ((a || b) :: rest)
  | xs => f xs

theorem duplicate_preserves_top (k : Nat) (f : List Bool → Bool) :
    parity (k+2) (duplicate f) = parity (k+1) f := by
  simp only [parity, duplicate, Bool.false_or, Bool.true_or]
  generalize parity k (fun xs => f (false :: xs)) = a
  generalize parity k (fun xs => f (true :: xs)) = b
  cases a <;> cases b <;> rfl

/-- The eight signs on a fixed triple exclude all assignments only when
    every optional clause is selected. -/
def base (bits : List Bool) : Bool := !(bits.all id)

theorem base_top : parity 8 base = true := by decide

def lifted : Nat → List Bool → Bool
  | 0 => base
  | j+1 => duplicate (lifted j)

theorem all_top (j : Nat) : parity (8+j) (lifted j) = true := by
  induction j with
  | zero => exact base_top
  | succ j ih =>
    have h := duplicate_preserves_top (7+j) (lifted j)
    have h₁ : 7+j+2 = 8+(j+1) := by omega
    have h₂ : 7+j+1 = 8+j := by omega
    rw [h₁, h₂] at h
    exact h.trans ih

end ClauseSelectorLift

namespace FreshClauseLift

def newPair (a b c z : Bool) : Bool := (a || b || z) && (a || c || !z)

/-- Existentially eliminating the one new variable recovers the old clause,
    for every fixed assignment to all old variables. -/
theorem resolves (a b c : Bool) :
    (newPair a b c false || newPair a b c true) = (a || b || c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Deleting either child makes the new variable able to satisfy its sibling. -/
theorem childDeletion (a b c : Bool) :
    (a || b || true) = true ∧ (a || c || !false) = true := by simp

end FreshClauseLift
