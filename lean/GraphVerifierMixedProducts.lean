import Std

namespace GraphVerifierMixedProducts

/-- A generating product of one function of each input direction. For jets of
    rational gates these two functions are linear forms. -/
abbrev Generator (K U V : Type) := (U → K) × (V → K)

def rankOne [Mul K] (g : Generator K U V) (u : U) (v : V) : K :=
  g.1 u * g.2 v

/-- Finite scalar linear combinations, expressed using their closure rules. -/
inductive InSpan {K U V : Type} [OfNat K 0] [Add K] [Neg K] [Mul K]
    (gs : List (Generator K U V)) : (U → V → K) → Prop
  | zero : InSpan gs (fun _ _ => 0)
  | generator (g : Generator K U V) (occurs : g ∈ gs) : InSpan gs (rankOne g)
  | add {f g} (hf : InSpan gs f) (hg : InSpan gs g) : InSpan gs (fun u v => f u v + g u v)
  | neg {f} (hf : InSpan gs f) : InSpan gs (fun u v => -(f u v))
  | scale (a : K) {f} (hf : InSpan gs f) : InSpan gs (fun u v => a * f u v)

theorem enlarge [OfNat K 0] [Add K] [Neg K] [Mul K]
    {xs ys : List (Generator K U V)} (inside : ∀ g ∈ xs, g ∈ ys)
    {f : U → V → K} (h : InSpan xs f) : InSpan ys f := by
  induction h with
  | zero => exact .zero
  | generator g occurs => exact .generator g (inside g occurs)
  | add _ _ ha hb => exact .add ha hb
  | neg _ ha => exact .neg ha
  | scale a _ ha => exact .scale a ha

structure Jet (K U V : Type) where
  base : K
  first : U → K
  second : V → K
  mixed : U → V → K

def mult [Add K] [Mul K] (p q : Jet K U V) : Jet K U V :=
  ⟨p.base * q.base,
    fun u => p.base * q.first u + q.base * p.first u,
    fun v => p.base * q.second v + q.base * p.second v,
    fun u v => p.base * q.mixed u v +
      (q.base * p.mixed u v + (p.first u * q.second v + q.first u * p.second v))⟩

def withCrossTerms (p q : Jet K U V) (gs : List (Generator K U V)) :=
  (p.first, q.second) :: (q.first, p.second) :: gs

theorem two_new (p q : Jet K U V) (gs : List (Generator K U V)) :
    (withCrossTerms p q gs).length = gs.length + 2 := rfl

private theorem old [OfNat K 0] [Add K] [Neg K] [Mul K] (p q : Jet K U V)
    {gs : List (Generator K U V)} {f : U → V → K} (h : InSpan gs f) :
    InSpan (withCrossTerms p q gs) f :=
  enlarge (fun _ hg => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)) h

private theorem cross [OfNat K 0] [Add K] [Neg K] [Mul K]
    (p q : Jet K U V) (gs : List (Generator K U V)) :
    InSpan (withCrossTerms p q gs)
      (fun u v => p.first u * q.second v + q.first u * p.second v) :=
  .add (.generator (p.first, q.second) List.mem_cons_self)
    (.generator (q.first, p.second) (List.mem_cons_of_mem _ List.mem_cons_self))

/-- A product gate extends a common list of generators by at most two products. -/
theorem product_gate [OfNat K 0] [Add K] [Neg K] [Mul K]
    (p q : Jet K U V) {gs : List (Generator K U V)}
    (hp : InSpan gs p.mixed) (hq : InSpan gs q.mixed) :
    InSpan (withCrossTerms p q gs) (mult p q).mixed :=
  .add (.scale p.base (old p q hq)) (.add (.scale q.base (old p q hp)) (cross p q gs))

/-- Only the particular ring identities used to isolate the mixed quotient
    are needed, so the proof has no external algebra-library dependency. -/
class ScalarLaws (K : Type) [OfNat K 0] [OfNat K 1] [Add K] [Mul K] [Neg K] : Prop where
  addAssoc (a b c : K) : (a + b) + c = a + (b + c)
  addNeg (a : K) : a + -a = 0
  addZero (a : K) : a + 0 = a
  mulAssoc (a b c : K) : (a * b) * c = a * (b * c)
  oneMul (a : K) : 1 * a = a

instance : ScalarLaws Int where
  addAssoc := Int.add_assoc
  addNeg := Int.add_right_neg
  addZero := Int.add_zero
  mulAssoc := Int.mul_assoc
  oneMul := Int.one_mul

section Quotient

variable [OfNat K 0] [OfNat K 1] [Add K] [Mul K] [Neg K] [ScalarLaws K]

/-- For a valid quotient h = p/q, where inv is the inverse of q.base, solve
    the mixed coefficient in q*h=p. All coefficients are evaluated at one base. -/
theorem quotient_identity (p q h : Jet K U V) (inv : K) (unit : inv * q.base = 1)
    (valid : mult q h = p) (u : U) (v : V) :
    h.mixed u v = inv * (p.mixed u v +
       -(h.base * q.mixed u v + (q.first u * h.second v + h.first u * q.second v))) := by
  have undo (a b : K) : (a + b) + -b = a := by
    rw [ScalarLaws.addAssoc, ScalarLaws.addNeg, ScalarLaws.addZero]
  rw [← valid]
  change h.mixed u v = inv * ((q.base * h.mixed u v + _) + -_)
  rw [undo, ← ScalarLaws.mulAssoc, unit, ScalarLaws.oneMul]

theorem quotient_gate (p q h : Jet K U V) (inv : K) (unit : inv * q.base = 1)
    (valid : mult q h = p) {gs : List (Generator K U V)}
    (hp : InSpan gs p.mixed) (hq : InSpan gs q.mixed) :
    InSpan (withCrossTerms q h gs) h.mixed := by
  have equation := funext (fun u => funext (quotient_identity p q h inv unit valid u))
  rw [equation]
  exact .scale inv (.add (old q h hp) (.neg (.add (.scale h.base (old q h hq)) (cross q h gs))))

/-- A growing list of available jets models sharing: any earlier gate output
    may be used again. A free stage must preserve every common linear span,
    as addition, subtraction, and multiplication by constants do. -/
inductive Stages {K U V : Type} [OfNat K 0] [OfNat K 1] [Add K] [Mul K] [Neg K] :
    List (Jet K U V) → Nat → Prop
  | inputs (xs : List (Jet K U V)) (zero : ∀ x ∈ xs, x.mixed = fun _ _ => 0) : Stages xs 0
  | linear {xs n} (before : Stages xs n) (z : Jet K U V)
      (preserves : ∀ gs, (∀ x ∈ xs, InSpan gs x.mixed) → InSpan gs z.mixed) :
      Stages (z :: xs) n
  | product {xs n} (before : Stages xs n) (p q : Jet K U V)
      (hp : p ∈ xs) (hq : q ∈ xs) : Stages (mult p q :: xs) (n + 1)
  | quotient {xs n} (before : Stages xs n) (p q h : Jet K U V)
      (hp : p ∈ xs) (hq : q ∈ xs) (inv : K) (unit : inv * q.base = 1)
      (valid : mult q h = p) : Stages (h :: xs) (n + 1)

omit [ScalarLaws K] [OfNat K 1] in
private theorem retain {gs : List (Generator K U V)} {xs : List (Jet K U V)}
    {z : Jet K U V} (fresh : InSpan gs z.mixed) (prior : ∀ x ∈ xs, InSpan gs x.mixed) :
    ∀ x ∈ z :: xs, InSpan gs x.mixed := by
  intro x used
  rcases List.mem_cons.mp used with rfl | earlier
  · exact fresh
  · exact prior x earlier

/-- One list of at most 2s generators spans all mixed outputs together,
    even when outputs are reused by later multiplication or division gates. -/
theorem simultaneous_basis {xs : List (Jet K U V)} {s : Nat} (built : Stages xs s) :
    ∃ gs : List (Generator K U V), gs.length ≤ 2 * s ∧ ∀ x ∈ xs, InSpan gs x.mixed := by
  induction built with
  | inputs xs zero =>
    refine ⟨[], by simp, ?_⟩
    intro x used
    rw [zero x used]
    exact .zero
  | linear before z preserves ih =>
    obtain ⟨gs, length, prior⟩ := ih
    exact ⟨gs, length, retain (preserves gs prior) prior⟩
  | product before p q hp hq ih =>
    obtain ⟨gs, length, prior⟩ := ih
    refine ⟨withCrossTerms p q gs, ?_, retain (product_gate p q (prior p hp) (prior q hq)) ?_⟩
    · rw [two_new]
      omega
    · exact fun x hx => old p q (prior x hx)
  | quotient before p q h hp hq inv unit valid ih =>
    obtain ⟨gs, length, prior⟩ := ih
    refine ⟨withCrossTerms q h gs, ?_,
      retain (quotient_gate p q h inv unit valid (prior p hp) (prior q hq)) ?_⟩
    · rw [two_new]
      omega
    · exact fun x hx => old q h (prior x hx)

end Quotient

end GraphVerifierMixedProducts
