import Std

/-! Boolean affine span for an arbitrary finite sequence of clause peelings.
An extension adds a coordinate to satisfy a clause. An old literal of that
clause must be capable of making the clause true without the new coordinate.
The last theorem concerns the numerical witness measure of a width-bounded
derivation. The expansion or girth of a particular hypergraph is external. -/

namespace PeelingAffineClauseFamilies

def Bits : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Bits n

def zero : (n : Nat) → Bits n
  | 0 => ()
  | n + 1 => (false, zero n)

def dot : {n : Nat} → Bits n → Bits n → Bool
  | 0, _, _ => false
  | _ + 1, (a, as), (x, xs) => (a && x).xor (dot as xs)

/-- The only equation valid throughout the set is the tautology 0 = 0. -/
def FullSpan {n : Nat} (models : Bits n → Prop) : Prop :=
  ∀ (a : Bits n) (b : Bool), (∀ x, models x → dot a x = b) →
    a = zero n ∧ b = false

/-- Project onto every old model. One double fiber suffices to remove the
new coefficient in any affine equation on the lifted models. -/
theorem extend_one {n : Nat} {old : Bits n → Prop} {new : Bits (n+1) → Prop}
    (full : FullSpan old)
    (hasLift : ∀ y, old y → ∃ v, new (v, y))
    (double : ∃ y : Bits n, new (false, y) ∧ new (true, y)) :
    FullSpan new := by
  rintro ⟨lead, tail⟩ b constant
  cases lead with
  | false =>
    have oldEq : ∀ y, old y → dot tail y = b := by
      intro y hy
      obtain ⟨v, hv⟩ := hasLift y hy
      simpa [dot] using constant (v, y) hv
    obtain ⟨ht, hb⟩ := full tail b oldEq
    exact ⟨by simp [zero, ht], hb⟩
  | true =>
    obtain ⟨y, hf, ht⟩ := double
    have a := constant (false, y) hf
    have c := constant (true, y) ht
    cases h : dot tail y <;> simp_all [dot]

theorem full_cube (n : Nat) : FullSpan (fun _ : Bits n => True) := by
  induction n with
  | zero =>
    rintro ⟨⟩ b h
    exact ⟨rfl, (h () trivial).symm⟩
  | succ n ih =>
    apply extend_one ih
    · exact fun _ _ => ⟨false, trivial⟩
    · exact ⟨zero n, trivial, trivial⟩

/-- A nonzero coefficient vector takes either prescribed value on a
full-span model set. This also handles an old literal of either polarity. -/
theorem attains_bit {n : Nat} {old : Bits n → Prop} (full : FullSpan old)
    (a : Bits n) (nonzero : a ≠ zero n) (b : Bool) :
    ∃ y, old y ∧ dot a y = b := by
  apply Classical.byContradiction
  intro missing
  have allOther : ∀ y, old y → dot a y = !b := by
    intro y hy
    have different : dot a y ≠ b := fun same => missing ⟨y, hy, same⟩
    cases b <;> cases h : dot a y <;> simp_all
  exact nonzero (full a (!b) allOther).1

/-- An ordinary positive or negative literal on one old coordinate is a
special case of the nonzero parity tested by the side condition. -/
def AddClause {n : Nat} (old : Bits n → Prop) (sign : Bool)
    (other : Bits n → Prop) (x : Bits (n+1)) : Prop :=
  old x.2 ∧ (x.1 = sign ∨ other x.2)

theorem peel_clause {n : Nat} {old : Bits n → Prop} (full : FullSpan old)
    (sign : Bool) (other : Bits n → Prop) (a : Bits n) (nonzero : a ≠ zero n)
    (b : Bool) (sufficient : ∀ y, dot a y = b → other y) :
    FullSpan (AddClause old sign other) := by
  apply extend_one full
  · intro y hy
    exact ⟨sign, hy, Or.inl rfl⟩
  · obtain ⟨y, hy, bit⟩ := attains_bit full a nonzero b
    exact ⟨y, ⟨hy, Or.inr (sufficient y bit)⟩, ⟨hy, Or.inr (sufficient y bit)⟩⟩

/-- A free cube can be extended by arbitrarily many proper peelings.
Unconstrained leftover variables can already be in the initial cube. -/
inductive Peelable : (n : Nat) → (Bits n → Prop) → Prop
  | cube (n : Nat) : Peelable n (fun _ => True)
  | clause {n : Nat} {old : Bits n → Prop} (prior : Peelable n old)
      (sign : Bool) (other : Bits n → Prop) (a : Bits n) (nonzero : a ≠ zero n)
      (b : Bool) (sufficient : ∀ y, dot a y = b → other y) :
      Peelable (n+1) (AddClause old sign other)

theorem full_span_of_peeling {n : Nat} {models : Bits n → Prop}
    (family : Peelable n models) : FullSpan models := by
  induction family with
  | cube n => exact full_cube n
  | clause _ sign other a nonzero b sufficient ih =>
    exact peel_clause ih sign other a nonzero b sufficient

inductive Position : Nat → Type
  | first {n : Nat} : Position (n+1)
  | later {n : Nat} (i : Position n) : Position (n+1)

def coord {n : Nat} (i : Position n) (y : Bits n) : Bool :=
  match i, y with
  | .first, (v, _) => v
  | .later j, (_, ys) => coord j ys

def unitVector {n : Nat} (i : Position n) : Bits n :=
  match i with
  | .first => (true, zero _)
  | .later j => (false, unitVector j)

theorem zero_dot {n : Nat} (y : Bits n) : dot (zero n) y = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨v, ys⟩ := y
    simp [zero, dot, ih]

theorem unit_dot {n : Nat} (i : Position n) (y : Bits n) :
    dot (unitVector i) y = coord i y := by
  induction i with
  | first =>
    obtain ⟨v, ys⟩ := y
    simp [unitVector, dot, coord, zero_dot]
  | later j ih =>
    obtain ⟨v, ys⟩ := y
    simp [unitVector, dot, coord, ih]

theorem unit_nonzero {n : Nat} (i : Position n) : unitVector i ≠ zero n := by
  induction i with
  | first =>
    intro eq
    have impossible : true = false := congrArg Prod.fst eq
    cases impossible
  | later j ih =>
    intro eq
    exact ih (congrArg Prod.snd eq)

/-- A syntactic family of proper 3-CNFs. At insertion the fresh head
coordinate occurs in the newly appended clause. The two old coordinates
are distinct. All three signs are independent and later clauses can reuse
any old coordinate. Reading the constructors backwards is a peeling order. -/
inductive TripleFormula : Nat → Type
  | empty (n : Nat) : TripleFormula n
  | append {n : Nat} (old : TripleFormula n) (i j : Position n)
      (distinct : i ≠ j) (headSign leftSign rightSign : Bool) :
      TripleFormula (n+1)

def Models {n : Nat} (formula : TripleFormula n) : Bits n → Prop :=
  match formula with
  | .empty _ => fun _ => True
  | .append old i j _ headSign leftSign rightSign =>
    AddClause (Models old) headSign
      (fun y => coord i y = leftSign ∨ coord j y = rightSign)

theorem proper_triples_peel {n : Nat} (formula : TripleFormula n) :
    Peelable n (Models formula) := by
  induction formula with
  | empty n => exact .cube n
  | append old i j _ headSign leftSign rightSign ih =>
    apply Peelable.clause ih headSign _ (unitVector i) (unit_nonzero i) leftSign
    intro y bit
    exact Or.inl ((unit_dot i y).symm.trans bit)

theorem all_peelable_triples_span {n : Nat} (formula : TripleFormula n) :
    FullSpan (Models formula) :=
  full_span_of_peeling (proper_triples_peel formula)

/-- A witness-measure model of weakening and binary resolution. Each
constructor asserts that the *actual* line has width at most the cap. -/
inductive Derivable {Line : Type} (width : Line → Nat) (cap : Nat)
    (axiomLine : Line → Prop) (weak : Line → Line → Prop)
    (resolve : Line → Line → Line → Prop) : Line → Prop
  | initial {d} (h : axiomLine d) (fits : width d ≤ cap) :
      Derivable width cap axiomLine weak resolve d
  | weaken {p d} (prior : Derivable width cap axiomLine weak resolve p)
      (h : weak p d) (fits : width d ≤ cap) :
      Derivable width cap axiomLine weak resolve d
  | resolution {p q d} (left : Derivable width cap axiomLine weak resolve p)
      (right : Derivable width cap axiomLine weak resolve q)
      (h : resolve p q d) (fits : width d ≤ cap) :
      Derivable width cap axiomLine weak resolve d

/-- For all finite derivations, the subadditive witness measure stays in
the small range, where the boundary-variable inequality applies. -/
theorem small_measure {Line : Type} {width mu : Line → Nat} {w s : Nat}
    {axiomLine : Line → Prop} {weak : Line → Line → Prop}
    {resolve : Line → Line → Line → Prop}
    (positive : 1 ≤ w) (budget : 8*w ≤ s)
    (initialCost : ∀ d, axiomLine d → mu d ≤ 1)
    (weakCost : ∀ p d, weak p d → mu d ≤ mu p)
    (sumCost : ∀ p q d, resolve p q d → mu d ≤ mu p + mu q)
    (boundary : ∀ d, mu d ≤ s → mu d ≤ 4 * width d) {d}
    (derivation : Derivable width w axiomLine weak resolve d) :
    mu d ≤ 4*w := by
  induction derivation with
  | initial h _ => have := initialCost _ h; omega
  | weaken _ h _ ih => exact Nat.le_trans (weakCost _ _ h) ih
  | resolution _ _ h fits lp lq =>
    have cost := sumCost _ _ _ h
    have inRange : _ ≤ s := Nat.le_trans cost (by omega)
    have bd := boundary _ inRange
    omega

end PeelingAffineClauseFamilies
