import Std

/-! An affine-triangle query accepts a union of intersections of three affine
bit predicates. The live-system lemma below works for arbitrary predicates. -/

namespace AffineTriangleOracle

abbrev V3 := Bool × Bool × Bool

def dot (x y : V3) : Bool :=
  (x.1 && y.1) ^^ (x.2.1 && y.2.1) ^^ (x.2.2 && y.2.2)

def cross (z x : V3) : V3 :=
  ((z.2.1 && x.2.2) ^^ (z.2.2 && x.2.1),
   (z.2.2 && x.1) ^^ (z.1 && x.2.2),
   (z.1 && x.2.1) ^^ (z.2.1 && x.1))

def words : List V3 :=
  [(false,false,false), (false,false,true), (false,true,false), (false,true,true),
   (true,false,false), (true,false,true), (true,true,false), (true,true,true)]

theorem nine_disjuncts (x y : V3) :
    (dot x y = false) ↔ x = (false,false,false) ∨
      words.any (fun z => decide (cross z x = y)) = true := by
  rcases x with ⟨a,b,c⟩
  rcases y with ⟨d,e,f⟩
  decide +revert

theorem orthogonal_iff (x y : V3) :
    dot x y = false ↔ x = (false,false,false) ∨ ∃ z : V3, cross z x = y := by
  have allWords (z : V3) : z ∈ words := by
    rcases z with ⟨a,b,c⟩
    decide +revert
  rw [nine_disjuncts]
  constructor
  · rintro (zero | yes)
    · exact Or.inl zero
    · obtain ⟨z, _, value⟩ := List.any_eq_true.mp yes
      exact Or.inr ⟨z, of_decide_eq_true value⟩
  · rintro (zero | ⟨z, hz⟩)
    · exact Or.inl zero
    · exact Or.inr (List.any_eq_true.mpr ⟨z, allWords z, decide_eq_true hz⟩)

def add (x y : V3) : V3 := (x.1 ^^ y.1, x.2.1 ^^ y.2.1, x.2.2 ^^ y.2.2)

/-- For each fixed z, testing y = cross z x costs three linear equations. -/
theorem cross_linear (z x y : V3) : cross z (add x y) = add (cross z x) (cross z y) := by
  rcases z with ⟨a,b,c⟩
  rcases x with ⟨d,e,f⟩
  rcases y with ⟨g,h,i⟩
  decide +revert

abbrev Triangle (A : Type) := A × A × A

def terms (t : Triangle A) : List A := [t.1, t.2.1, t.2.2]

inductive Tree (A Label : Type) where
  | leaf (label : Label)
  | ask (triangles : List (Triangle A)) (yes no : Tree A Label)

def depth : Tree A Label → Nat
  | .leaf _ => 0
  | .ask _ yes no => max (depth yes) (depth no) + 1

def run (atom : X → A → Bool) (x : X) : Tree A Label → Label
  | .leaf label => label
  | .ask ts yes no =>
      if ts.any (fun t => (terms t).all (atom x)) then run atom x yes else run atom x no

def Live (atom : X → A → Bool) (constraints : List A) (x : X) : Prop :=
  constraints.all (atom x) = true

private theorem live_append (atom : X → A → Bool) (x : X) (a b : List A) :
    Live atom (a ++ b) x ↔ Live atom a x ∧ Live atom b x := by
  simp [Live, List.all_append]

/-- On some nonempty subfamily described by at most three extra atoms per
query, the full adaptive strategy selects a fixed leaf label. The labels can
stand for affine output forms to be evaluated after the transcript. -/
theorem live_leaf (atom : X → A → Bool) (tree : Tree A Label) (initial : List A)
    (start : ∃ x, Live atom initial x) :
    ∃ (extra : List A) (label : Label), extra.length ≤ 3 * depth tree ∧
      (∃ x, Live atom (initial ++ extra) x) ∧
      (∀ x, Live atom (initial ++ extra) x → run atom x tree = label) := by
  induction tree generalizing initial with
  | leaf label => exact ⟨[], label, by simp [depth], by simpa using start, fun _ _ => rfl⟩
  | ask ts yes no ihYes ihNo =>
    by_cases feasible : ∃ (x : X) (t : Triangle A), Live atom initial x ∧ t ∈ ts ∧ Live atom (terms t) x
    · obtain ⟨x₀, t, init, mem, hit⟩ := feasible
      have ext := (live_append atom x₀ initial (terms t)).mpr ⟨init,hit⟩
      obtain ⟨rest, label, count, nonempty, follows⟩ := ihYes (initial ++ terms t) ⟨x₀, ext⟩
      refine ⟨terms t ++ rest, label, ?_, by simpa [List.append_assoc] using nonempty, ?_⟩
      · have bound := Nat.le_max_left (depth yes) (depth no)
        simp [terms,depth]
        omega
      · intro x hx
        have allLive : Live atom ((initial ++ terms t) ++ rest) x := by simpa [List.append_assoc] using hx
        have ht := ((live_append _ _ _ _).mp ((live_append _ _ _ _).mp allLive).1).2
        have positive : ts.any (fun a => (terms a).all (atom x)) = true :=
          List.any_eq_true.mpr ⟨t,mem,ht⟩
        simpa [run,positive] using follows x allLive
    · obtain ⟨extra, label, count, nonempty, follows⟩ := ihNo initial start
      refine ⟨extra, label, ?_, nonempty, ?_⟩
      · have bound := Nat.le_max_right (depth yes) (depth no)
        simp [depth]
        omega
      · intro x hx
        have hi := ((live_append _ _ _ _).mp hx).1
        have negative : ts.any (fun a => (terms a).all (atom x)) ≠ true := by
          intro h
          obtain ⟨t, hm, ht⟩ := List.any_eq_true.mp h
          exact feasible ⟨x, t, hi, hm, ht⟩
        simpa [run,negative] using follows x hx

#print axioms orthogonal_iff
#print axioms cross_linear
#print axioms live_leaf

end AffineTriangleOracle
