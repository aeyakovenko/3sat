import Std

/-! Byte accounting for greedy clause packs, and evaluation of one-hole contexts. -/

namespace ClausePackBounds

/-- Two consecutive pack sizes cannot fit together. -/
def AdjacentOverflow (budget : Nat) : List Nat → Prop
  | first :: second :: rest =>
    budget < first + second ∧ AdjacentOverflow budget (second :: rest)
  | _ => True

private theorem overflow_tail {budget first : Nat} {rest : List Nat}
    (h : AdjacentOverflow budget (first :: rest)) : AdjacentOverflow budget rest := by
  cases rest with
  | nil => trivial
  | cons second rest => exact h.2

/-- Pairing consecutive packs pays for their count, with one allowance for the last pack. -/
theorem pack_length_bound (budget : Nat) : ∀ sizes : List Nat,
    AdjacentOverflow budget sizes → sizes.length * budget ≤ 2 * sizes.sum + budget
  | [], _ => by simp
  | [size], _ => by simp
  | first :: second :: rest, h => by
    have pair : budget < first + second := h.1
    have remaining := pack_length_bound budget rest (overflow_tail h.2)
    simp only [List.length_cons, List.sum_cons, Nat.succ_mul]
    omega

/-- A separate final-pack allowance for each run suffices, including empty runs. -/
theorem runs_length_bound (budget : Nat) (runs : List (List Nat))
    (h : ∀ run ∈ runs, AdjacentOverflow budget run) :
    runs.flatten.length * budget ≤ 2 * (runs.map List.sum).sum + runs.length * budget := by
  induction runs with
  | nil => simp
  | cons run rest ih =>
    have headBound := pack_length_bound budget run (h run (by simp))
    have tailBound := ih (fun tail ht => h tail (by simp [ht]))
    simp only [List.flatten_cons, List.length_append, Nat.add_mul, List.map_cons,
      List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Siblings have been evaluated. Each node on the path specifies which child contains the hole. -/
inductive Context where
  | hole
  | unary (op : Bool → Bool) (inner : Context)
  | left (op : Bool → Bool → Bool) (inner : Context) (sibling : Bool)
  | right (op : Bool → Bool → Bool) (sibling : Bool) (inner : Context)

namespace Context

def eval : Context → Bool → Bool
  | .hole, bit => bit
  | .unary op inner, bit => op (inner.eval bit)
  | .left op inner sibling, bit => op (inner.eval bit) sibling
  | .right op sibling inner, bit => op sibling (inner.eval bit)

def plug : Context → Context → Context
  | .hole, replacement => replacement
  | .unary op inner, replacement => .unary op (inner.plug replacement)
  | .left op inner sibling, replacement => .left op (inner.plug replacement) sibling
  | .right op sibling inner, replacement => .right op sibling (inner.plug replacement)

theorem eval_plug (outer inner : Context) (bit : Bool) :
    (outer.plug inner).eval bit = outer.eval (inner.eval bit) := by
  induction outer <;> simp [plug, eval, *]

/-- The outer catalog's two outputs suffice also when the hole is a whole context. -/
theorem eval_plug_from_two_outputs (outer inner : Context) (bit : Bool) :
    (outer.plug inner).eval bit = cond (inner.eval bit) (outer.eval true) (outer.eval false) := by
  rw [eval_plug]
  cases inner.eval bit <;> rfl

end Context
end ClausePackBounds
