import Std

namespace PrivateClauseTree

/-- Edge flags are propositions about one fixed Boolean assignment. -/
inductive Tree where
  | leaf (emit payload : Prop)
  | branch (emit toLeft toRight : Prop) (left right : Tree)

def up : Tree → Prop
  | .leaf emit _ => emit
  | .branch emit _ _ _ _ => emit

/-- The leaf side condition abbreviates all blocker clauses at this leaf:
    when emitting without input, every literal in its payload clause is false. -/
def valid : Tree → Prop → Prop
  | .leaf emit payload, incoming =>
    (payload ∨ incoming) ∧ (emit → incoming ∨ ¬payload)
  | .branch emit toLeft toRight left right, incoming =>
    (emit → up left ∨ up right) ∧
    (toLeft → incoming ∨ up right) ∧
    (toRight → incoming ∨ up left) ∧
    ¬(up left ∧ up right) ∧
    valid left toLeft ∧ valid right toRight

/-- All leaf clauses hold, and no internal edge carries a signal. -/
def solved : Tree → Prop
  | .leaf _ payload => payload
  | .branch _ toLeft toRight left right =>
    ¬toLeft ∧ ¬toRight ∧ ¬up left ∧ ¬up right ∧ solved left ∧ solved right

theorem no_incoming (tree : Tree) (incoming : Prop) (off : ¬incoming)
    (h : valid tree incoming) : ¬up tree ∧ solved tree := by
  induction tree generalizing incoming with
  | leaf emit payload =>
    obtain ⟨demand, blocker⟩ := h
    have holds : payload := demand.elim id (fun b => (off b).elim)
    exact ⟨fun e => (blocker e).elim off (fun bad => bad holds), holds⟩
  | branch emit toLeft toRight left right ihLeft ihRight =>
    obtain ⟨upRelay, leftRelay, rightRelay, excl, hLeft, hRight⟩ := h
    have leftOff : ¬up left := by
      intro leftOn
      have rightOff : ¬up right := fun rightOn => excl ⟨leftOn, rightOn⟩
      have inputOff : ¬toLeft := fun sent => (leftRelay sent).elim off rightOff
      exact (ihLeft toLeft inputOff hLeft).1 leftOn
    have rightInputOff : ¬toRight := fun sent => (rightRelay sent).elim off leftOff
    have rightResult := ihRight toRight rightInputOff hRight
    have leftInputOff : ¬toLeft := fun sent => (leftRelay sent).elim off rightResult.1
    have leftResult := ihLeft toLeft leftInputOff hLeft
    exact ⟨fun sent => (upRelay sent).elim leftOff rightResult.1,
           leftInputOff, rightInputOff, leftOff, rightResult.1, leftResult.2, rightResult.2⟩

theorem root_payloads (tree : Tree) (h : valid tree False) : solved tree :=
  (no_incoming tree False id h).2

end PrivateClauseTree
