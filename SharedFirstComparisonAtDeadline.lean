import Std

namespace SharedFirstComparisonAtDeadline

universe u
variable {State : Type u}

/-- A fixed-label unrolling. Only a binary test changes the subsequent instruction labels. -/
inductive Program (State : Type u) where
  | halt (verdict : Bool)
  | work (update : State → State) (next : Program State)
  | test (condition : State → Bool) (next : Bool → Program State)

/-- A terminal is free, and either a data instruction or a branch consumes one step. -/
def observed : Nat → Program State → State → Option Bool
  | _, .halt v, _ => some v
  | 0, .work _ _, _ => none
  | 0, .test _ _, _ => none
  | n+1, .work update next, s => observed n next (update s)
  | n+1, .test condition next, s => observed n (next (condition s)) s

def chain : List (State → State) → Program State → Program State
  | [], tail => tail
  | f :: rest, tail => .work f (chain rest tail)

def advance : List (State → State) → State → State
  | [], s => s
  | f :: rest, s => advance rest (f s)

theorem chain_cost (ops : List (State → State)) (n : Nat) (tail : Program State)
    (s : State) : observed (ops.length+n) (chain ops tail) s =
      observed n tail (advance ops s) := by
  induction ops generalizing s with
  | nil => simp [chain,advance]
  | cons f rest ih =>
    simp only [chain,advance,List.length_cons]
    rw [Nat.add_right_comm]
    exact ih (f s)

/-- At zero remaining time, the outcome of a fixed child is independent of state. -/
theorem zero_fixed (tail : Program State) (left right : State) :
    observed 0 tail left = observed 0 tail right := by
  cases tail <;> rfl

/-- All targets finishing by the shared first comparison must take the outcome
opposite to any marked file forbidden from accepting. No runtime bound on that
marked file beyond this point is required. -/
theorem targets_take_opposite (ops : List (State → State)) (choose : State → Bool)
    (tail : Bool → Program State) (target : State → Prop) (neg : State)
    (accepted : ∀ x, target x →
      observed (ops.length+1) (chain ops (.test choose tail)) x = some true)
    (sound : observed (ops.length+1) (chain ops (.test choose tail)) neg ≠ some true)
    (x : State) (isTarget : target x) :
    choose (advance ops x) = !(choose (advance ops neg)) := by
  have hx := accepted x isTarget
  rw [chain_cost] at hx sound
  simp only [observed] at hx sound
  have diff : choose (advance ops x) ≠ choose (advance ops neg) := by
    intro same
    apply sound
    rw [same,zero_fixed _ (advance ops x) (advance ops neg)] at hx
    exact hx
  cases h : choose (advance ops x) <;> cases k : choose (advance ops neg) <;> simp_all

end SharedFirstComparisonAtDeadline
