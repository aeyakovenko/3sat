import Std

namespace SignedTreeStorage

inductive Tree where
  | leaf
  | fork (left right : Tree)

def leaves : Tree → Nat
  | .leaf => 1
  | .fork l r => leaves l + leaves r

/-- Visit a subtree with fewer leaves first, leaving its sibling pending. -/
def pending : Tree → Nat
  | .leaf => 0
  | .fork l r =>
    if leaves l ≤ leaves r then max (pending l + 1) (pending r)
    else max (pending r + 1) (pending l)

private theorem forkBound {p q a b : Nat} (pa : 2^p ≤ a) (qb : 2^q ≤ b)
    (ab : a ≤ b) : 2 ^ max (p+1) q ≤ a+b := by
  by_cases h : p+1 ≤ q
  · rw [Nat.max_eq_right h]
    omega
  · have h' : q ≤ p+1 := by omega
    rw [Nat.max_eq_left h', Nat.pow_succ]
    omega

theorem pending_bound (tree : Tree) : 2 ^ pending tree ≤ leaves tree := by
  induction tree with
  | leaf => decide
  | fork l r hl hr =>
    simp only [pending, leaves]
    split
    · exact forkBound hl hr ‹_›
    · have h : leaves r ≤ leaves l := by omega
      rw [Nat.add_comm (leaves l)]
      exact forkBound hr hl h

/-- When querying the actual output rail, a false response contradicts its
honest forward rule as soon as all predecessor rails have been established. -/
theorem gate_branch {premises rail : Prop} (h : premises)
    (forwardRule : premises → rail) : ¬ rail → False := fun hfalse => hfalse (forwardRule h)

/-- Either truth value for the requested pin is covered by forbidding the
opposite rail in a two-rail least model. -/
theorem pin_exact (actual requested : Bool) :
    (¬ actual = !requested) ↔ actual = requested := by
  cases actual <;> cases requested <;> decide

end SignedTreeStorage
