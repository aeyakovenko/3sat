import Std

namespace LastResetWitnessReader

inductive Action where
  | keep | flip | zero | one
  deriving DecidableEq

def act : Action → Bool → Bool
  | .keep, x => x
  | .flip, x => !x
  | .zero, _ => false
  | .one, _ => true

def decode (f : Bool → Bool) : Action :=
  match f false, f true with
  | false, false => .zero
  | false, true => .keep
  | true, false => .flip
  | true, true => .one

theorem decode_correct (f : Bool → Bool) (x : Bool) : act (decode f) x = f x := by
  cases h : f false <;> cases k : f true <;> cases x <;> simp [decode, act, h, k]

def perm : Action → Bool
  | .keep | .flip => true
  | _ => false

def run (q : Bool) : List Action → Bool
  | [] => q
  | a :: l => run (act a q) l

def survives : List Action → Bool
  | [] => true
  | a :: l => perm a && survives l

def phase : List Action → Bool
  | [] => false
  | a :: l => xor (act a false) (phase l)

def bit (x : Bool) : Nat := if x then 1 else 0

def countResets (goal : Bool) : List Action → Nat
  | [] => 0
  | a :: l => countResets goal l +
      bit ((!perm a) && survives l && (xor (act a false) (phase l) == goal))

/-- For each fixed valuation, the no-reset event and the last-reset events
account for precisely one acceptance if the actual final state is the target. -/
theorem partition (l : List Action) (q goal : Bool) :
    countResets goal l + bit (survives l && (xor q (phase l) == goal)) =
      bit (run q l == goal) := by
  induction l generalizing q with
  | nil => cases q <;> cases goal <;> rfl
  | cons a l ih =>
    rw [run, ← ih (act a q)]
    cases a <;> cases q <;> cases goal <;> cases hs : survives l <;>
      cases hp : phase l <;> simp [act, perm, survives, phase, countResets, hs, hp, bit]

structure Row (I : Type) where
  name : I
  delta : Bool → Bool → Bool

def actions {I : Type} (x : I → Bool) (rows : List (Row I)) : List Action :=
  rows.map fun r => decode (r.delta (x r.name))

def eval {I : Type} (x : I → Bool) (q : Bool) : List (Row I) → Bool
  | [] => q
  | r :: rs => eval x (r.delta (x r.name) q) rs

theorem run_actions {I : Type} (x : I → Bool) (rows : List (Row I)) (q : Bool) :
    run q (actions x rows) = eval x q rows := by
  induction rows generalizing q with
  | nil => rfl
  | cons r rs ih => simp [actions, run, eval, decode_correct, ← ih, actions]

theorem reader_partition {I : Type} (x : I → Bool) (rows : List (Row I)) (q goal : Bool) :
    countResets goal (actions x rows) +
      bit (survives (actions x rows) && (xor q (phase (actions x rows)) == goal)) =
      bit (eval x q rows == goal) := by
  rw [← run_actions]
  exact partition _ _ _

/-- The witness address can depend on the current state. Both destination
bits are still fixed unary maps once the whole witness has been chosen. -/
structure AdaptiveRow (I : Type) where
  name : Bool → I
  next : Bool → Bool → Bool

def actual {I : Type} (x : I → Bool) (r : AdaptiveRow I) (q : Bool) :=
  r.next q (x (r.name q))

def adaptiveEval {I : Type} (x : I → Bool) (q : Bool) : List (AdaptiveRow I) → Bool
  | [] => q
  | r :: rs => adaptiveEval x (actual x r q) rs

theorem adaptive_run {I : Type} (x : I → Bool) (rs : List (AdaptiveRow I)) (q : Bool) :
    run q (rs.map (fun r => decode (actual x r))) = adaptiveEval x q rs := by
  induction rs generalizing q with
  | nil => rfl
  | cons r rs ih => simp [run, decode_correct, adaptiveEval, ih]

theorem adaptive_partition {I : Type} (x : I → Bool) (rs : List (AdaptiveRow I)) (q goal : Bool) :
    let l := rs.map (fun r => decode (actual x r))
    countResets goal l + bit (survives l && (xor q (phase l) == goal)) =
      bit (adaptiveEval x q rs == goal) := by
  dsimp only
  rw [← adaptive_run x rs q]
  exact partition _ _ _

end LastResetWitnessReader
