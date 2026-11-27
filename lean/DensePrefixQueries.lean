import Std

namespace DensePrefixQueries

/-- A finite tree of output weights in common integral units. -/
inductive Tree where
  | leaf (weight : Nat)
  | fork (left right : Tree)

def mass : Tree → Nat
  | .leaf n => n
  | .fork l r => mass l + mass r

/-- Use zero for a position that does not end at a leaf. -/
def atPath : Tree → List Bool → Nat
  | .leaf n, [] => n
  | .fork l _, false :: rest => atPath l rest
  | .fork _ r, true :: rest => atPath r rest
  | _, _ => 0

theorem pathBound (t : Tree) (bits : List Bool) : atPath t bits ≤ mass t := by
  induction t generalizing bits with
  | leaf n => cases bits <;> simp [atPath, mass]
  | fork l r il ir =>
    cases bits with
    | nil => simp [atPath]
    | cons b bs =>
      cases b
      · exact Nat.le_trans (il bs) (Nat.le_add_right _ _)
      · exact Nat.le_trans (ir bs) (Nat.le_add_left _ _)

def kept (answer : Tree → Bool) : Tree → List Bool → Bool
  | t, [] => match t with
    | .leaf _ => answer t
    | .fork _ _ => false
  | .fork l r, b :: bs => answer (.fork l r) && (if b then kept answer r bs else kept answer l bs)
  | .leaf _, _ :: _ => false

/-- Completeness holds for any fixed answers in the intermediate interval. -/
theorem heavySurvives (answer : Tree → Bool) (high : Nat) (positive : 0 < high)
    (complete : ∀ t, high ≤ mass t → answer t = true)
    (t : Tree) (bits : List Bool) (heavy : high ≤ atPath t bits) :
    kept answer t bits = true := by
  have head := complete t (Nat.le_trans heavy (pathBound t bits))
  induction t generalizing bits with
  | leaf n =>
    cases bits with
    | nil => exact head
    | cons b bs => simp [atPath] at heavy; omega
  | fork l r il ir =>
    cases bits with
    | nil => simp [atPath] at heavy; omega
    | cons b bs =>
      cases b with
      | false =>
        have h : high ≤ atPath l bs := heavy
        simp [kept, head, il bs h (complete l (Nat.le_trans h (pathBound l bs)))]
      | true =>
        have h : high ≤ atPath r bs := heavy
        simp [kept, head, ir bs h (complete r (Nat.le_trans h (pathBound r bs)))]

/-- Number of yes nodes at a single level, pruned below any no node. -/
def frontier (answer : Tree → Bool) : Tree → Nat → Nat
  | t, 0 => if answer t then 1 else 0
  | .leaf _, _+1 => 0
  | .fork l r, j+1 =>
      if answer (.fork l r) then frontier answer l j + frontier answer r j else 0

theorem frontierMass (answer : Tree → Bool) (low : Nat)
    (sound : ∀ t, answer t = true → low ≤ mass t)
    (t : Tree) (j : Nat) :
    low * frontier answer t j ≤ mass t := by
  induction j generalizing t with
  | zero =>
    by_cases a : answer t = true
    · simpa [frontier, a] using sound t a
    · simp [frontier, a]
  | succ j ih =>
    cases t with
    | leaf n => simp [frontier, mass]
    | fork l r =>
      by_cases a : answer (.fork l r) = true
      · simpa [frontier, a, Nat.mul_add, mass] using Nat.add_le_add (ih l) (ih r)
      · simp [frontier, a]

end DensePrefixQueries
