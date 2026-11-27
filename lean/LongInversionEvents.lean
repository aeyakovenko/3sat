import Std

namespace LongInversionEvents

structure Row where
  key : Nat
  drop : Bool

/-- Relative order is required for all pairs outside the deletion cover. -/
def covered (a b : Row) : Prop :=
  a.drop = false → b.drop = false → a.key ≤ b.key

def pops : List Row → List Row → Nat
  | _, [] => 0
  | [], x :: xs => pops [x] xs
  | y :: ys, x :: xs =>
    if x.key < y.key then 1 + pops ys xs else pops (x :: y :: ys) xs

/-- The actual greedy stack has at most one pop per member of any deletion
    cover. At a pop the adjacent pair in reverse-stack ++ unread-suffix
    contains a member of the cover. The two rows are then removed forever. -/
theorem pops_le_cover (remaining stack : List Row)
    (order : (stack.reverse ++ remaining).Pairwise covered) :
    pops stack remaining ≤ (stack.reverse ++ remaining).countP Row.drop := by
  induction remaining generalizing stack with
  | nil => simp [pops]
  | cons x xs ih =>
    cases stack with
    | nil =>
      simpa [pops] using ih [x] (by simpa using order)
    | cons y ys =>
      have combined : (ys.reverse ++ y :: x :: xs).Pairwise covered := by
        simpa [List.reverse_cons, List.append_assoc] using order
      by_cases hinv : x.key < y.key
      · have pair : covered y x :=
          (List.pairwise_cons.mp (List.pairwise_append.mp combined).2.1).1 x (by simp)
        have marked : y.drop = true ∨ x.drop = true := by
          cases hy : y.drop <;> cases hx : x.drop <;> simp_all [covered] <;> omega
        have sub : xs.Sublist (y :: x :: xs) :=
          .cons y (.cons x (.refl xs))
        have hnext := ih ys (List.Pairwise.sublist (sub.append_left ys.reverse) combined)
        simp only [pops, if_pos hinv, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.countP_append, List.countP_cons, List.countP_nil, List.countP_reverse] at hnext ⊢
        rcases marked with hy | hx
        · simp [hy]; omega
        · simp [hx]; omega
      · have hnext := ih (x :: y :: ys) (by
          simpa [List.reverse_cons, List.append_assoc] using combined)
        simpa [pops, hinv, List.reverse_cons, List.append_assoc] using hnext

end LongInversionEvents
