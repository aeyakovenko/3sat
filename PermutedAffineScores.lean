import Std

/-! Clause-score identity and complete affine permutation orbit. Boolean lists are in variable
order. The two equal-length lists are the selected and unselected non-anchor variables. -/

namespace PermutedAffineScores

def bit : Bool → Nat
  | false => 0
  | true => 1

def ones : List Bool → Nat
  | [] => 0
  | x :: xs => bit x + ones xs

theorem ones_append (xs ys : List Bool) : ones (xs ++ ys) = ones xs + ones ys := by
  induction xs with
  | nil => simp [ones]
  | cons x xs ih => simp [ones, ih, Nat.add_assoc]

theorem ones_le_length (xs : List Bool) : ones xs ≤ xs.length := by
  induction xs with
  | nil => simp [ones]
  | cons x xs ih => cases x <;> simp [ones, bit] <;> omega

theorem perm_ones {xs ys : List Bool} (h : xs.Perm ys) : ones xs = ones ys := by
  induction h with
  | nil => rfl
  | cons x h ih => simp [ones, ih]
  | swap x y xs => simp [ones]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Number of failures of the clause (a ∨ b ∨ c). -/
def bad (a b c : Bool) : Nat := bit (!(a || b || c))

/-- Splitting a binary clause on any third name preserves its zero test. -/
theorem split_fails (a b z : Bool) : bad a b z + bad a b (!z) = bit (!(a || b)) := by
  cases a <;> cases b <;> cases z <;> rfl

/-- The three split binary forbiddances isolate exactly the anchor values (true,false). -/
theorem anchors (a b x y z : Bool) :
    bad a b x + bad a b (!x) + (bad a (!b) y + bad a (!b) (!y)) +
      (bad (!a) (!b) z + bad (!a) (!b) (!z)) = 0 ↔ a = true ∧ b = false := by
  rw [split_fails, split_fails, split_fails]
  cases a <;> cases b <;> decide

def singles (a b : Bool) : List Bool → Nat
  | [] => 0
  | x :: xs => bad (!a) b (!x) + singles a b xs

def pairs (a b : Bool) : List Bool → Nat
  | [] => 0
  | x :: xs => (bad (!a) b x + bad (!a) b (!x)) + pairs a b xs

theorem singles_count (a b : Bool) (xs : List Bool) :
    singles a b xs = if a && !b then ones xs else 0 := by
  induction xs with
  | nil => cases a <;> cases b <;> rfl
  | cons x xs ih => cases a <;> cases b <;> cases x <;> simp_all [singles, ones, bad, bit]

theorem pairs_count (a b : Bool) (xs : List Bool) :
    pairs a b xs = if a && !b then xs.length else 0 := by
  induction xs with
  | nil => cases a <;> cases b <;> rfl
  | cons x xs ih =>
    rw [pairs, split_fails, ih]
    cases a <;> cases b <;> simp [bit] <;> omega

/-- The common score may depend arbitrarily on this assignment. -/
theorem difference (common : Nat) (a b : Bool) (xs ys : List Bool) :
    ((common + singles a b (xs ++ ys) : Nat) : Int) - ((common + pairs a b xs : Nat) : Int) =
    if a && !b then (ones (a :: b :: (xs ++ ys)) : Int) - (1 + (xs.length : Int)) else 0 := by
  rw [singles_count, pairs_count]
  cases a <;> cases b <;> simp [ones, bit] <;> omega

theorem orbit_scores (common : Nat) (a b : Bool) (xs ys : List Bool)
    (same : xs.length = ys.length)
    (orbit : ones (a :: b :: (xs ++ ys)) = 0 ∨
      2 * ones (a :: b :: (xs ++ ys)) = (a :: b :: (xs ++ ys)).length ∨
      ones (a :: b :: (xs ++ ys)) = (a :: b :: (xs ++ ys)).length) :
    common + singles a b (xs ++ ys) = common + pairs a b xs := by
  have hi := ones_le_length (xs ++ ys)
  rw [singles_count, pairs_count]
  cases a <;> cases b <;> simp_all [ones, bit] <;> omega

/-- Address bits are read most significant first; hence the two halves of the truth table. -/
def affine : List Bool → Bool → List Bool
  | [], bias => [bias]
  | c :: cs, bias => affine cs bias ++ affine cs (bias != c)

theorem affine_length (cs : List Bool) (bias : Bool) :
    (affine cs bias).length = 2 ^ cs.length := by
  induction cs generalizing bias with
  | nil => simp [affine]
  | cons c cs ih => simp [affine, ih, Nat.pow_succ]; omega

theorem opposite_biases (cs : List Bool) :
    ones (affine cs false) + ones (affine cs true) = 2 ^ cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [affine, ones_append, Nat.pow_succ] <;> omega

theorem affine_weights (cs : List Bool) (bias : Bool) :
    ones (affine cs bias) = 0 ∨ 2 * ones (affine cs bias) = 2 ^ cs.length ∨
      ones (affine cs bias) = 2 ^ cs.length := by
  induction cs generalizing bias with
  | nil => cases bias <;> decide
  | cons c cs ih =>
    have half := opposite_biases cs
    have no := ih false
    have yes := ih true
    cases c <;> cases bias <;> simp [affine, ones_append, Nat.pow_succ] <;> omega

/-- Arbitrarily permuting the address assignment before scoring preserves the equality. -/
theorem affine_permuted_scores (common : Nat) (a b : Bool) (xs ys cs : List Bool) (bias : Bool)
    (same : xs.length = ys.length) (ordering : (a :: b :: (xs ++ ys)).Perm (affine cs bias)) :
    common + singles a b (xs ++ ys) = common + pairs a b xs := by
  apply orbit_scores _ _ _ _ _ same
  rw [perm_ones ordering, ordering.length_eq, affine_length]
  exact affine_weights cs bias

/-- Adding one complement twin per original variable fixes the total pair weight. -/
theorem complement_twins (xs : List Bool) : ones (xs ++ xs.map Bool.not) = xs.length := by
  rw [ones_append]
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [ones, bit] <;> omega

end PermutedAffineScores
