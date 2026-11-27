import Std

/- Fix the true bits and work array. At a compatible node either the reply
   is forced, or two surviving edges use the true word and the forecast. -/
namespace SparseReplyPaths

inductive Tree where
  | dead
  | leaf (label : Nat)
  | forced (child : Tree)
  | fork (forecast actual : Tree)

inductive Reaches : Tree → List Bool → Nat → Prop where
  | leaf (label) : Reaches (.leaf label) [] label
  | forced : Reaches t w i → Reaches (.forced t) w i
  | forecast : Reaches l w i → Reaches (.fork l r) (false :: w) i
  | actual : Reaches r w i → Reaches (.fork l r) (true :: w) i

def replay : Tree → List Bool → Option Nat
  | .leaf label, [] => some label
  | .forced child, tokens => replay child tokens
  | .fork l _, false :: tokens => replay l tokens
  | .fork _ r, true :: tokens => replay r tokens
  | _, _ => none

theorem replay_recovers (h : Reaches tree word label) :
    replay tree word = some label := by
  induction h with
  | leaf => rfl
  | forced _ ih => exact ih
  | forecast _ ih => exact ih
  | actual _ ih => exact ih

theorem code_determines_leaf (a : Reaches tree word i) (b : Reaches tree word j) :
    i = j := Option.some.inj ((replay_recovers a).symm.trans (replay_recovers b))

/-- Pascal's rectangle counts binary words with exactly e zeros and j ones. -/
def wordCount : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 1
  | e + 1, j + 1 => wordCount e (j + 1) + wordCount (e + 1) j

def leafCount : Tree → Nat → Nat → Nat
  | .dead, _, _ => 0
  | .leaf _, 0, 0 => 1
  | .leaf _, _, _ => 0
  | .forced t, e, j => leafCount t e j
  | .fork _ _, 0, 0 => 0
  | .fork l _, e + 1, 0 => leafCount l e 0
  | .fork _ r, 0, j + 1 => leafCount r 0 j
  | .fork l r, e + 1, j + 1 => leafCount l e (j + 1) + leafCount r (e + 1) j

theorem compatible_count (tree : Tree) (e j : Nat) :
    leafCount tree e j ≤ wordCount e j := by
  induction tree generalizing e j with
  | dead => simp [leafCount]
  | leaf label =>
    cases e <;> cases j <;> simp [leafCount, wordCount]
  | forced t ih => exact ih e j
  | fork l r hl hr =>
    cases e with
    | zero =>
      cases j with
      | zero => simp [leafCount, wordCount]
      | succ j => simpa only [leafCount, wordCount] using hr 0 j
    | succ e =>
      cases j with
      | zero =>
        have h := hl e 0
        cases e <;> simpa only [leafCount, wordCount] using h
      | succ j => simpa only [leafCount, wordCount] using Nat.add_le_add (hl e (j+1)) (hr (e+1) j)

end SparseReplyPaths
