import Std

namespace GrammarCell

/-- The effect of a string of records projected onto one address. -/
inductive Summary where
  | impossible
  | live (required replacement : Option Nat)

def run (summary : Summary) (initial : Nat) : Option Nat :=
  match summary with
  | .impossible => none
  | .live none w => some (w.getD initial)
  | .live (some n) w => if initial = n then some (w.getD initial) else none

private def last (earlier later : Option Nat) : Option Nat :=
  match later with
  | none => earlier
  | some v => some v

def thenDo (left right : Summary) : Summary :=
  match left, right with
  | .impossible, _ | _, .impossible => .impossible
  | .live a w, .live none v => .live a (last w v)
  | .live a (some w), .live (some b) v =>
      if w = b then .live a (last (some w) v) else .impossible
  | .live none none, .live (some b) v => .live (some b) v
  | .live (some a) none, .live (some b) v =>
      if a = b then .live (some a) v else .impossible

theorem run_thenDo (left right : Summary) (initial : Nat) :
    run (thenDo left right) initial = (run left initial).bind (run right) := by
  cases left with
  | impossible => simp [thenDo, run]
  | live a w =>
    cases right with
    | impossible =>
      cases a <;> cases w <;> simp [thenDo, run] <;> split <;> rfl
    | live b v =>
      by_cases entry : initial = a.getD 0 <;>
        by_cases second : initial = b.getD 0 <;>
        by_cases writes : w.getD 0 = b.getD 0 <;>
        by_cases guards : a.getD 0 = b.getD 0 <;>
        cases a <;> cases w <;> cases b <;> cases v <;>
        simp_all [thenDo, run, last]

end GrammarCell
