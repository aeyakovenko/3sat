import Std

/-! The explicit eight-clause contradiction and the root separation argument.
    The external structure theorem for minimally unsatisfiable formulas of
    deficiency one is cited in the accompanying manuscript. -/
namespace GrowingSat

structure Literal where
  var : Nat
  negated : Bool
  deriving DecidableEq

abbrev Clause := Literal × Literal × Literal

def pos (x : Nat) : Literal := ⟨x,false⟩
def neg (x : Nat) : Literal := ⟨x,true⟩

def witness (d e f : Nat) : List Clause :=
  [(pos 1, pos 2, pos 3), (pos 1, neg 2, pos d),
   (pos 2, neg 3, pos e), (neg 2, neg d, pos f),
   (neg 1, pos 2, pos 3), (neg 1, neg 2, pos d),
   (pos 2, neg 3, neg e), (neg 2, neg d, neg f)]

def truth (v : Nat → Bool) (c : Clause) : Bool :=
  let literal := fun a : Literal => v a.var ^^ a.negated
  literal c.1 || literal c.2.1 || literal c.2.2

private theorem paired_contradiction (a b c d e f : Bool) :
    ((a || b || c) && (a || !b || d) && (b || !c || e) && (!b || !d || f) &&
    (!a || b || c) && (!a || !b || d) && (b || !c || !e) && (!b || !d || !f)) = false := by
  decide +revert

theorem no_model (d e f : Nat) (v : Nat → Bool) :
    ((witness d e f).all (truth v)) = false := by
  simpa [witness, truth, pos, neg, Bool.and_assoc] using
    paired_contradiction (v 1) (v 2) (v 3) (v d) (v e) (v f)

def proper (n : Nat) (c : Clause) : Bool :=
  let a := c.1.var
  let b := c.2.1.var
  let d := c.2.2.var
  (a != b) && (b != d) && (a != d) &&
    decide (0 < a ∧ a ≤ n ∧ 0 < b ∧ b ≤ n ∧ 0 < d ∧ d ≤ n)

def layout (n : Nat) (cs : List Clause) : Bool :=
  decide (3 ≤ n ∧ n - 2 ≤ cs.length) && cs.all (proper n) &&
  ((cs.take (n - 2)).zipIdx).all fun (c,i) =>
    max c.1.var (max c.2.1.var c.2.2.var) == i + 3

/-- First n-2 clauses introduce all variables in order; remaining clauses close the instance. -/
theorem four_layouts :
    [(3, witness 3 1 1),(4, witness 4 1 1),(5, witness 4 5 1),(6, witness 4 5 6)].all
      (fun (n,cs) => layout n cs && (cs.length - (n - 2) == 10 - n)) = true := by decide

/-- Abstract two-parent growth for any orientation of the ordered clauses. -/
inductive Closure (seed : α → Prop) (steps : α → α → α → Prop) : α → Prop where
  | initial {x} : seed x → Closure seed steps x
  | step {u v x} : steps u v x → u ≠ v → Closure seed steps u → Closure seed steps v →
                   Closure seed steps x

theorem closure_stays_on_one_side (seed : α → Prop) (steps : α → α → α → Prop)
    (left right : α → Prop) (seed_left : ∀ x, seed x → left x)
    (split : ∀ u v x, steps u v x →
      (left u ∧ left v ∧ left x) ∨ (right u ∧ right v ∧ right x))
    (overlap : ∀ u v, left u → left v → right u → right v → u = v)
    {x} (grown : Closure seed steps x) : left x := by
  induction grown with
  | initial h => exact seed_left _ h
  | step he different _ _ hu hv =>
    rcases split _ _ _ he with hl | hr
    · exact hl.2.2
    · exact False.elim (different (overlap _ _ hu hv hr.1 hr.2.1))

#print axioms no_model
#print axioms four_layouts
#print axioms closure_stays_on_one_side
end GrowingSat
