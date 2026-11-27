import Std

/-! Ranks of touches at a single address. The no-predecessor code is zero;
a link to rank j has code j+1. Distinct keys and strictly backward links
force the list's actual consecutive-touch relation. -/

namespace TouchPredecessors

theorem consecutive {n : Nat} (key : Nat → Nat)
    (backward : ∀ i, i < n → key i ≤ i)
    (unique : ∀ i j, i < n → j < n → key i = key j → i = j) :
    ∀ i, i < n → key i = i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    have le := backward i hi
    apply Classical.byContradiction
    intro neq
    have lt : key i < i := by omega
    have hit := ih (key i) lt (by omega)
    have equal := unique (key i) i (by omega) hi hit
    omega

inductive Operation (Word : Type) where
  | read
  | write (value : Word)

def advance {Word : Type} (old : Word) : Operation Word → Word
  | .read => old
  | .write value => value

/-- Array state immediately before the indicated touch at one address. -/
def memory {Word : Type} (initial : Word) (op : Nat → Operation Word) : Nat → Word
  | 0 => initial
  | j+1 => advance (memory initial op j) (op j)

/-- 'After' is the value stored/checkable in each chronological row. -/
def prior {Word : Type} (initial : Word) (after : Nat → Word) : Nat → Word
  | 0 => initial
  | j+1 => after j

theorem checkedReplies {Word : Type} {n : Nat} (initial : Word)
    (op : Nat → Operation Word) (after : Nat → Word) (key : Nat → Nat)
    (backward : ∀ i, i < n → key i ≤ i)
    (unique : ∀ i j, i < n → j < n → key i = key j → i = j)
    (check : ∀ i, i < n → after i = advance (prior initial after (key i)) (op i)) :
    ∀ i, i < n → prior initial after (key i) = memory initial op i ∧
      after i = memory initial op (i+1) := by
  have ranks := consecutive key backward unique
  intro i
  induction i with
  | zero =>
    intro hi
    rw [ranks 0 hi]
    constructor
    · rfl
    · simpa [ranks 0 hi, prior, memory] using check 0 hi
  | succ i ih =>
    intro hi
    have correct := (ih (by omega)).2
    have prev : prior initial after (key (i+1)) = memory initial op (i+1) := by
      simpa [ranks (i+1) hi, prior] using correct
    exact ⟨prev, (check (i+1) hi).trans (congrArg (fun v => advance v (op (i+1))) prev)⟩

end TouchPredecessors
