import Std.Tactic.BVDecide

namespace FifthSelectorWordUpper

abbrev W := BitVec 5

/-- The last bit is either a negative-unit selector or a selector enabling
an extra disjunct. The two meanings use opposite physical bits on the old slice. -/
inductive Flag where
  | negativeUnit
  | enableDisjunct

structure File where
  p : W
  q : W
  m : W
  n : W
  z : Bool

def bitWord (z : Bool) : W := if z then 1 else 0

def freeFlag : Flag → Bool → Bool
  | .negativeUnit, z => !z
  | .enableDisjunct, z => z

def fits (kind : Flag) (f : File) : Prop :=
  f.p &&& f.m = 0 ∧ f.q &&& f.n = 0 ∧
  (f.m ≠ 31 ∨ f.n ≠ 31 ∨ freeFlag kind f.z = true)

/-- `u` may satisfy the fixed final disjunction exactly when the new variable
is free, or equivalently when its extra disjunct has been enabled. -/
def hasModel (kind : Flag) (f : File) : Prop :=
  ∃ (x y : W) (u : Bool), f.p &&& x = f.p ∧ f.q &&& y = f.q ∧
    f.m &&& x = 0 ∧ f.n &&& y = 0 ∧ (u = false ∨ freeFlag kind f.z = true) ∧
    (x ≠ 0 ∨ y ≠ 0 ∨ u = true)

theorem semantic (kind : Flag) (f : File) : hasModel kind f ↔ fits kind f := by
  rcases f with ⟨p,q,m,n,z⟩
  constructor
  · rintro ⟨x,y,u,hp,hq,hm,hn,hu,hs⟩
    cases kind <;> cases z <;> cases u <;> simp_all [fits, freeFlag] <;> bv_decide
  · intro h
    refine ⟨~~~m, ~~~n, freeFlag kind z, ?_⟩
    cases kind <;> cases z <;> simp_all [fits, freeFlag] <;> bv_decide

/-- The same instruction is used for literal and register-indirect loads. -/
inductive Code where
  | halt (v : Bool)
  | load (address : W) (next : W → Code)
  | band (a b : W) (next : W → Code)
  | eq (a b : W) (yes no : Code)
  | ult (a b : W) (yes no : Code)

def memory (f : File) (a : W) : W :=
  if a = 0 then f.p else if a = 1 then f.q else if a = 2 then f.m else
  if a = 3 then f.n else if a = 4 then bitWord f.z else 0

def run (f : File) : Code → Bool × Nat
  | .halt v => (v,0)
  | .load a k => let r := run f (k (memory f a)); (r.1,r.2+1)
  | .band a b k => let r := run f (k (a &&& b)); (r.1,r.2+1)
  | .eq a b yes no => let r := if a=b then run f yes else run f no; (r.1,r.2+1)
  | .ult a b yes no => let r := if a<b then run f yes else run f no; (r.1,r.2+1)

def disjoint (a b : W) : Code :=
  .band a b fun r => .eq r 0 (.halt true) (.halt false)

def lastThree : Flag → Code
  | .negativeUnit => .load 4 fun z => .load z fun x => .eq x z (.halt true) (.halt false)
  | .enableDisjunct => .load 0 fun p => .load 4 fun z => .ult p z (.halt true) (.halt false)

/-- This is a single fixed-label instruction tree at each meaning of `kind`.
No instruction labels are chosen from a loaded word except by a charged comparison. -/
def program (kind : Flag) : Code := .load 3 fun n =>
  .eq n 31
    (.load 1 fun q => .eq q 0
      (.load 2 fun m => .eq m 31 (lastThree kind) (.load 0 fun p => disjoint p m))
      (.halt false))
    (.load 1 fun q => .band q n fun v => .eq v 0
      (.load 0 fun p => .load 2 fun m => disjoint p m) (.halt false))

private theorem runSpec (kind : Flag) (f : File) :
    ((run f (program kind)).1 = true ↔ fits kind f) ∧ (run f (program kind)).2 ≤ 9 := by
  rcases f with ⟨p,q,m,n,z⟩
  by_cases hn : n = 31 <;> by_cases hq : q = 0 <;>
    by_cases hm : m = 31 <;> by_cases hqn : q &&& n = 0 <;>
    by_cases hpm : p &&& m = 0 <;> cases z <;> cases kind <;>
    simp_all [program, lastThree, disjoint, run, memory, bitWord, fits, freeFlag] <;>
    first | bv_decide | (split <;> simp_all <;> bv_decide)

theorem correct_and_bounded (kind : Flag) (f : File) :
    ((run f (program kind)).1 = true ↔ hasModel kind f) ∧ (run f (program kind)).2 ≤ 9 :=
  ⟨(runSpec kind f).1.trans (semantic kind f).symm, (runSpec kind f).2⟩

theorem attained (kind : Flag) : run ⟨4,4,11,11,false⟩ (program kind) = (true,9) := by
  cases kind <;> decide

/-- A finite chain of worst-case optima cannot increase at every successor
between these two endpoint clocks. -/
theorem no_strict_chain (T : Nat → Nat) (left : T 16 = 9) (right : T 21 ≤ 9) :
    ∃ n, 16 ≤ n ∧ n < 21 ∧ T (n+1) ≤ T n := by
  apply Classical.byContradiction
  intro h
  have rise (n : Nat) (lo : 16 ≤ n) (hi : n < 21) : T n < T (n+1) := by
    by_cases hr : T n < T (n+1)
    · exact hr
    · exact (h ⟨n, lo, hi, by omega⟩).elim
  have a : T 16 < T 17 := rise 16 (by decide) (by decide)
  have b : T 17 < T 18 := rise 17 (by decide) (by decide)
  have c : T 18 < T 19 := rise 18 (by decide) (by decide)
  have d : T 19 < T 20 := rise 19 (by decide) (by decide)
  have e : T 20 < T 21 := rise 20 (by decide) (by decide)
  omega

end FifthSelectorWordUpper

#print axioms FifthSelectorWordUpper.correct_and_bounded
#print axioms FifthSelectorWordUpper.no_strict_chain
