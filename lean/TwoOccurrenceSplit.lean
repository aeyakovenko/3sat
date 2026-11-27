import Std

namespace TwoOccurrenceSplit

def bit : Bool → Nat
  | false => 0
  | true => 1

def Split (p x y : Bool) : Prop := bit p = bit x + bit y

theorem split_affine_clause (p x y : Bool) :
    Split p x y ↔ p = (x ^^ y) ∧ ¬(x = true ∧ y = true) := by
  cases p <;> cases x <;> cases y <;> simp [Split, bit]

theorem signed_split_exactly_one (x y z : Bool) :
    Split (!x) y z ↔ bit x + bit y + bit z = 1 := by
  cases x <;> cases y <;> cases z <;> simp [Split, bit]

inductive Tree where
  | leaf (mark : Bool)
  | fork (left right : Tree)

def marks : Tree → Nat
  | .leaf b => bit b
  | .fork l r => marks l + marks r

def feasible : Tree → Bool → Prop
  | .leaf b, root => b = root
  | .fork l r, root =>
      ∃ x y, feasible l x ∧ feasible r y ∧ Split root x y

theorem capacity_tree (tree : Tree) (p : Bool) :
    feasible tree p ↔ marks tree = bit p := by
  induction tree generalizing p with
  | leaf b => cases b <;> cases p <;> simp [feasible, marks, bit]
  | fork l r hl hr =>
    simp only [feasible, marks, hl, hr, Split]
    constructor
    · rintro ⟨x, y, hx, hy, eq⟩
      omega
    · intro eq
      have bp : bit p ≤ 1 := by cases p <;> decide
      have encode (m : Nat) (hm : m ≤ 1) : ∃ b : Bool, m = bit b := by
        cases m with
        | zero => exact ⟨false, rfl⟩
        | succ m =>
          have : m = 0 := by omega
          subst m
          exact ⟨true, rfl⟩
      obtain ⟨x, hx⟩ := encode (marks l) (by omega)
      obtain ⟨y, hy⟩ := encode (marks r) (by omega)
      exact ⟨x, y, hx, hy, by omega⟩

inductive LabelledTree where
  | leaf (b : Bool)
  | fork (root : Bool) (left right : LabelledTree)

def rootBit : LabelledTree → Bool
  | .leaf b | .fork b _ _ => b

def leafCount : LabelledTree → Nat
  | .leaf b => bit b
  | .fork _ l r => leafCount l + leafCount r

def splitFailures : LabelledTree → Nat
  | .leaf _ => 0
  | .fork b l r =>
    (if bit b = bit (rootBit l) + bit (rootBit r) then 0 else 1) +
      splitFailures l + splitFailures r

theorem faulty_tree_capacity (tree : LabelledTree) :
    leafCount tree ≤ bit (rootBit tree) + 2 * splitFailures tree := by
  induction tree with
  | leaf b => simp [leafCount, rootBit, splitFailures]
  | fork b l r hl hr =>
    change leafCount l + leafCount r ≤ bit b + 2 *
      ((if bit b = bit (rootBit l) + bit (rootBit r) then 0 else 1) +
      splitFailures l + splitFailures r)
    have bitsmall (x : Bool) : bit x ≤ 1 := by cases x <;> decide
    have h₁ := bitsmall (rootBit l)
    have h₂ := bitsmall (rootBit r)
    split <;> omega

theorem six_bins_gap (n leftBad rightBad marksTotal : Nat)
    (demand : 2*n ≤ marksTotal + leftBad)
    (capacity : marksTotal ≤ n + 2*rightBad) :
    n ≤ 2*(leftBad + rightBad) := by omega

end TwoOccurrenceSplit
