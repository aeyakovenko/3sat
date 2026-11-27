import Std

namespace NativeTraceForestCharging

/-- Every primitive function may implement a width-specific native operation. -/
inductive Expr where
  | literal (v : Nat)
  | input (address : Nat)
  | gate (f : Nat → Nat → Nat) (x y : Expr)

def eval (assignment : Nat → Nat) : Expr → Nat
  | .literal v => v
  | .input a => assignment a
  | .gate f x y => f (eval assignment x) (eval assignment y)

structure State (α : Type) where
  registers : Nat → α
  memory : Nat → α

def interpret (v : Nat → Nat) (s : State Expr) : State Nat :=
  ⟨fun i => eval v (s.registers i), fun i => eval v (s.memory i)⟩

def set {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j=i then v else f j

inductive Arg where | reg (r : Nat) | lit (v : Nat)

def symbolicArg (s : State Expr) : Arg → Expr
  | .reg r => s.registers r
  | .lit k => .literal k

def valueArg (s : State Nat) : Arg → Nat
  | .reg r => s.registers r
  | .lit k => k

theorem arg_evaluation (v : Nat → Nat) (s : State Expr) (a : Arg) :
    valueArg (interpret v s) a = eval v (symbolicArg s a) := by
  cases a <;> rfl

/-- The finite base trace records its concrete load/store addresses and branch outcomes.
The concrete executor below uses each register address dynamically. -/
inductive Row where
  | alu (reg : Nat) (f : Nat → Nat → Nat) (a b : Arg)
  | load (reg : Nat) (address : Arg) (baseAddress : Nat)
  | store (address value : Arg) (baseAddress : Nat)
  | branch (test : Nat → Nat → Bool) (a b : Arg) (baseOutcome : Bool)

def symbolic (s : State Expr) : Row → State Expr
  | .alu r f a b => ⟨set s.registers r (.gate f (symbolicArg s a) (symbolicArg s b)), s.memory⟩
  | .load r _ i => ⟨set s.registers r (s.memory i), s.memory⟩
  | .store _ a i => ⟨s.registers, set s.memory i (symbolicArg s a)⟩
  | .branch .. => s

def observed (s : State Nat) : Row → Option (State Nat)
  | .alu r f a b => some ⟨set s.registers r (f (valueArg s a) (valueArg s b)), s.memory⟩
  | .load r a _ => some ⟨set s.registers r (s.memory (valueArg s a)), s.memory⟩
  | .store a b _ => some ⟨s.registers, set s.memory (valueArg s a) (valueArg s b)⟩
  | .branch test a b expected => if test (valueArg s a) (valueArg s b) = expected then some s else none

def satisfies (v : Nat → Nat) (s : State Expr) : Row → Prop
  | .alu .. => True
  | .load _ a i | .store a _ i => eval v (symbolicArg s a) = i
  | .branch test a b expected => test (eval v (symbolicArg s a)) (eval v (symbolicArg s b)) = expected

private theorem eval_set (v : Nat → Nat) (t : Nat → Expr) (j : Nat) (x : Expr) :
    (fun i => eval v (set t j x i)) = set (fun i => eval v (t i)) j (eval v x) := by
  funext i
  by_cases h : i=j <;> simp [set,h]

theorem row_replay (r : Row) (s : State Expr) (v : Nat → Nat) (h : satisfies v s r) :
    observed (interpret v s) r = some (interpret v (symbolic s r)) := by
  cases r with
  | alu i f a b => simp only [observed,symbolic,arg_evaluation]; simp only [interpret,eval_set,eval]
  | load i a j => simp only [satisfies] at h; simp only [observed,symbolic,arg_evaluation,h]; simp only [interpret,eval_set]
  | store a b j => simp only [satisfies] at h; simp only [observed,symbolic,arg_evaluation,h]; simp only [interpret,eval_set]
  | branch f a b out => simp only [satisfies] at h; simp only [observed,symbolic,arg_evaluation,h,if_pos]

def allChecks (v : Nat → Nat) (s : State Expr) : List Row → Prop
  | [] => True
  | r::rs => satisfies v s r ∧ allChecks v (symbolic s r) rs

def finalState (s : State Expr) : List Row → State Expr
  | [] => s
  | r::rs => finalState (symbolic s r) rs

def execute (s : State Nat) : List Row → Option (State Nat)
  | [] => some s
  | r::rs => (observed s r).bind (fun s' => execute s' rs)

theorem trace_replay (rows : List Row) (s : State Expr) (v : Nat → Nat)
    (h : allChecks v s rows) :
    execute (interpret v s) rows = some (interpret v (finalState s rows)) := by
  induction rows generalizing s with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨head,tail⟩ := h
    simp only [execute, finalState, row_replay r s v head, Option.bind_some]
    exact ih _ tail

/-- `paid` counts arithmetic operations, observed native branches, and charged
nonmandatory address tests. `small` and `large` count unanchored trees. -/
theorem forest_budget (m time paid small large h exceptions : Nat)
    (clock : m + paid ≤ time) (component_count : m ≤ paid + small + large)
    (component_sizes : small + (h+1)*large ≤ m) (pinned : small ≤ exceptions) :
    (2*h+1)*m ≤ (h+1)*time + h*exceptions := by
  have c := Nat.mul_le_mul_left (h+1) clock
  have d := Nat.mul_le_mul_left (h+1) component_count
  have e := Nat.mul_le_mul_left h pinned
  simp [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at c d component_sizes ⊢
  omega

/-- If every unanchored tree admits a perturbation even with the free pins,
there are no such components and the accounting is exactly two per word. -/
theorem all_trees (m time paid : Nat) (clock : m+paid ≤ time) (anchored : m ≤ paid) :
    2*m ≤ time := by omega

end NativeTraceForestCharging

#print axioms NativeTraceForestCharging.trace_replay
#print axioms NativeTraceForestCharging.forest_budget
