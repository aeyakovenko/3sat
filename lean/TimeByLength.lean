import Std

namespace TimeByLength

/-- Early coverage weights scaled to a common denominator. -/
def manyEarly (threshold : Nat) (weights : List Nat) : Nat :=
  (weights.filter (fun w => decide (threshold ≤ w))).length

theorem countCost (threshold : Nat) (weights : List Nat) :
    manyEarly threshold weights * threshold ≤ weights.sum := by
  induction weights with
  | nil => simp [manyEarly]
  | cons w rest ih =>
    by_cases hw : threshold ≤ w
    · simpa [manyEarly, hw, Nat.succ_mul, Nat.add_mul, Nat.add_comm] using Nat.add_le_add hw ih
    · simp only [manyEarly, List.filter_cons, decide_eq_true_eq, hw,
        if_false, List.sum_cons]
      exact Nat.le_trans ih (by omega)

/-- The bad members of the initial fully-covered segment also count against
    the budget for the entire block. -/
theorem badInSegment (threshold : Nat) (segment remaining : List Nat) :
    manyEarly threshold segment * threshold ≤ (segment ++ remaining).sum := by
  have sub : segment.sum ≤ (segment ++ remaining).sum := by
    induction segment with
    | nil => simp
    | cons x xs ih => simpa using Nat.add_le_add_left ih x
  exact Nat.le_trans (countCost threshold segment) sub

end TimeByLength
