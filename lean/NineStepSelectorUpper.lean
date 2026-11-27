import Std.Tactic.BVDecide

namespace NineStepSelectorUpper

abbrev W := BitVec 4

/-- Four initial memory words in physical order P0, P1, M0, M1. -/
structure File where
  p : W
  q : W
  m : W
  n : W

def hasModel (f : File) : Prop :=
  ∃ x y : W, (f.p &&& x) = f.p ∧ (f.q &&& y) = f.q ∧
    (f.m &&& x) = 0 ∧ (f.n &&& y) = 0 ∧ (x ≠ 0 ∨ y ≠ 0)

def fits (f : File) : Prop :=
  (f.p &&& f.m) = 0 ∧ (f.q &&& f.n) = 0 ∧ (f.m ≠ 15 ∨ f.n ≠ 15)

theorem semantic (f : File) : hasModel f ↔ fits f := by
  rcases f with ⟨p,q,m,n⟩
  constructor
  · rintro ⟨x,y,hp,hq,hm,hn,hxy⟩
    simp only [fits] at *
    bv_decide
  · intro hf
    refine ⟨~~~m, ~~~n, ?_⟩
    simp only [fits] at *
    bv_decide

/-- A fragment of native code. Values are named by continuations like registers.
Terminals take zero instructions; a load, AND or binary comparison takes one. -/
inductive Code where
  | halt (yes : Bool)
  | load (address : Fin 4) (next : W → Code)
  | andWord (a b : W) (next : W → Code)
  | branchEq (a b : W) (yes no : Code)

def peek (f : File) (i : Fin 4) : W :=
  if i = 0 then f.p else if i = 1 then f.q else if i = 2 then f.m else f.n

def execute (f : File) : Code → Bool × Nat
  | .halt v => (v, 0)
  | .load i k =>
    let r := execute f (k (peek f i))
    (r.1, r.2 + 1)
  | .andWord a b k =>
    let r := execute f (k (a &&& b))
    (r.1, r.2 + 1)
  | .branchEq a b yes no =>
    let r := if a = b then execute f yes else execute f no
    (r.1, r.2 + 1)

def test (a b : W) : Code :=
  .andWord a b fun t => .branchEq t 0 (.halt true) (.halt false)

def program : Code := .load 2 fun m =>
  .branchEq m 15
    (.load 3 fun n => .branchEq n 15 (.halt false)
      (.load 0 fun p => .branchEq p 0 (.load 1 fun q => test q n) (.halt false)))
    (.load 0 fun p => .andWord p m fun u => .branchEq u 0
      (.load 1 fun q => .load 3 fun n => test q n) (.halt false))

private theorem runSpec (f : File) :
    ((execute f program).1 = true ↔ fits f) ∧ (execute f program).2 ≤ 9 := by
  rcases f with ⟨p,q,m,n⟩
  by_cases hm : m = 15 <;> by_cases hn : n = 15 <;>
    by_cases hp : p = 0 <;> by_cases hu : p &&& m = 0 <;>
    by_cases hv : q &&& n = 0 <;>
    simp_all [program, test, execute, peek, fits] <;> bv_decide

theorem correct_and_bounded (f : File) :
    ((execute f program).1 = true ↔ hasModel f) ∧ (execute f program).2 ≤ 9 :=
  ⟨(runSpec f).1.trans (semantic f).symm, (runSpec f).2⟩

theorem attained : execute ⟨4,4,11,11⟩ program = (true,9) := by decide

end NineStepSelectorUpper

#print axioms NineStepSelectorUpper.correct_and_bounded
