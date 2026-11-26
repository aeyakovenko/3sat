import Std

/-!
Two-point affine restrictions over F₂. Programs can reuse all preceding wires.
An affine gate is free and a product of two affine combinations costs one AND.
Every displayed equation is an affine form on the original input set, set to
zero. The conclusions count equations directly and allow redundant equations.
-/
namespace TwoPointGateRestriction

inductive Aff (I : Type) where
  | bit (i : I)
  | lit (b : Bool)
  | add (a b : Aff I)

namespace Aff

def eval {I : Type} (x : I → Bool) : Aff I → Bool
  | .bit i => x i
  | .lit b => b
  | .add a b => xor (eval x a) (eval x b)

def subst {I J : Type} (w : J → Aff I) : Aff J → Aff I
  | .bit j => w j
  | .lit b => .lit b
  | .add a b => .add (subst w a) (subst w b)

theorem eval_subst {I J : Type} (x : I → Bool) (w : J → Aff I) (a : Aff J) :
    eval x (subst w a) = eval (fun j => eval x (w j)) a := by
  induction a <;> simp_all [subst, eval]

end Aff

/-- `none` is the new wire, `some j` is the original wire named `j`. -/
def extend {J T : Type} (a : T) (w : J → T) : Option J → T
  | none => a
  | some j => w j

inductive Program (I : Type) : Type → Type 1 where
  | inputs : Program I I
  | affine {J : Type} (p : Program I J) (a : Aff J) : Program I (Option J)
  | prod {J : Type} (p : Program I J) (a b : Aff J) : Program I (Option J)

namespace Program

def run {I J : Type} (p : Program I J) (x : I → Bool) : J → Bool :=
  match p with
  | .inputs => x
  | .affine t a => extend (a.eval (t.run x)) (t.run x)
  | .prod t a b => extend (a.eval (t.run x) && b.eval (t.run x)) (t.run x)

def ands {I J : Type} : Program I J → Nat
  | .inputs => 0
  | .affine t _ => t.ands
  | .prod t _ _ => t.ands + 1

end Program

def Flat {I : Type} (eqs : List (Aff I)) (x : I → Bool) : Prop :=
  ∀ e ∈ eqs, e.eval x = false

theorem flat_cons {I : Type} {e : Aff I} {eqs : List (Aff I)} {x : I → Bool} :
    Flat (e :: eqs) x ↔ e.eval x = false ∧ Flat eqs x := by
  simp [Flat]

/-- Lines specified by a constant first operand, second operand, or their XOR. -/
private inductive Line where
  | first (c : Bool)
  | second (c : Bool)
  | diagonal (c : Bool)

private def choose (a₀ b₀ a₁ b₁ : Bool) : Line :=
  if a₀ == a₁ then .first a₀
  else if b₀ == b₁ then .second b₀
  else .diagonal (xor a₀ b₀)

private def eqOf {I : Type} (l : Line) (a b : Aff I) : Aff I :=
  match l with
  | .first c => .add a (.lit c)
  | .second c => .add b (.lit c)
  | .diagonal c => .add (.add a b) (.lit c)

private def productOn {I : Type} (l : Line) (a b : Aff I) : Aff I :=
  match l with
  | .first c => if c then b else .lit false
  | .second c => if c then a else .lit false
  | .diagonal c => if c then .lit false else a

private theorem choose_contains {I : Type} (a b : Aff I) (x y : I → Bool) :
    let l := choose (a.eval x) (b.eval x) (a.eval y) (b.eval y)
    (eqOf l a b).eval x = false ∧ (eqOf l a b).eval y = false := by
  dsimp only
  cases hax : a.eval x <;> cases hbx : b.eval x <;>
    cases hay : a.eval y <;> cases hby : b.eval y <;>
    simp [choose, eqOf, Aff.eval, hax, hbx, hay, hby]

private theorem on_line {I : Type} (l : Line) (a b : Aff I) (x : I → Bool)
    (h : (eqOf l a b).eval x = false) :
    (a.eval x && b.eval x) = (productOn l a b).eval x := by
  cases l with
  | first c | second c | diagonal c =>
    cases c <;> cases ha : a.eval x <;> cases hb : b.eval x <;>
      simp_all [eqOf, productOn, Aff.eval]

/-- Simultaneous linearization of every input and computed wire, on a single
flat containing both designated inputs. The affine representatives have no
dependence on the original circuit's intermediate wires. -/
theorem all_wires {I J : Type} (p : Program I J) (u v : I → Bool) :
    ∃ (eqs : List (Aff I)) (w : J → Aff I),
      eqs.length ≤ p.ands ∧ Flat eqs u ∧ Flat eqs v ∧
      ∀ (x : I → Bool), Flat eqs x → ∀ j, p.run x j = (w j).eval x := by
  induction p with
  | inputs =>
    exact ⟨[], Aff.bit, Nat.le_refl _, by simp [Flat], by simp [Flat],
      fun _ _ _ => rfl⟩
  | affine p a ih =>
    obtain ⟨eqs, w, size, hu, hv, agree⟩ := ih
    refine ⟨eqs, extend (a.subst w) w, size, hu, hv, ?_⟩
    intro x hx j
    cases j with
    | none =>
      change a.eval (p.run x) = (a.subst w).eval x
      rw [Aff.eval_subst, funext (agree x hx)]
    | some j => exact agree x hx j
  | prod p a b ih =>
    obtain ⟨eqs, w, size, hu, hv, agree⟩ := ih
    let A := a.subst w
    let B := b.subst w
    let l := choose (A.eval u) (B.eval u) (A.eval v) (B.eval v)
    have both := choose_contains A B u v
    refine ⟨eqOf l A B :: eqs, extend (productOn l A B) w,
      Nat.succ_le_succ size, flat_cons.mpr ⟨both.1, hu⟩,
      flat_cons.mpr ⟨both.2, hv⟩, ?_⟩
    intro x hx j
    obtain ⟨line, old⟩ := flat_cons.mp hx
    cases j with
    | none =>
      change (a.eval (p.run x) && b.eval (p.run x)) = (productOn l A B).eval x
      rw [funext (agree x old), ← Aff.eval_subst, ← Aff.eval_subst]
      exact on_line l A B x line
    | some j => exact agree x old j

/-- When an arbitrary affine readout has the same verdict at the two points,
one further affine input equation fixes that verdict throughout the flat. -/
theorem constant_output_flat {I J : Type} (p : Program I J) (out : Aff J)
    (u v : I → Bool) (c : Bool)
    (hu : out.eval (p.run u) = c) (hv : out.eval (p.run v) = c) :
    ∃ eqs : List (Aff I), eqs.length ≤ p.ands + 1 ∧ Flat eqs u ∧ Flat eqs v ∧
      ∀ (x : I → Bool), Flat eqs x → out.eval (p.run x) = c := by
  obtain ⟨old, w, size, oldU, oldV, agree⟩ := all_wires p u v
  let a := out.subst w
  have readout (x : I → Bool) (hx : Flat old x) : out.eval (p.run x) = a.eval x := by
    rw [funext (agree x hx)]
    exact (Aff.eval_subst x w out).symm
  have zeros (x : I → Bool) : (Aff.add a (.lit c)).eval x = false ↔ a.eval x = c := by
    cases ha : a.eval x <;> cases c <;> simp [Aff.eval, ha]
  exact ⟨.add a (.lit c) :: old, Nat.succ_le_succ size,
    flat_cons.mpr ⟨(zeros u).mpr ((readout u oldU).symm.trans hu), oldU⟩,
    flat_cons.mpr ⟨(zeros v).mpr ((readout v oldV).symm.trans hv), oldV⟩,
    fun x h => (readout x (flat_cons.mp h).2).trans ((zeros x).mp (flat_cons.mp h).1)⟩

/-! Projecting hidden input bits preserves the equation budget. The elimination
below uses a pivot with coefficient 1 if one exists, and projects exactly. -/

private def firstCoeff {I : Type} : Aff (Option I) → Bool
  | .bit none => true
  | .bit (some _) => false
  | .lit _ => false
  | .add a b => xor (firstCoeff a) (firstCoeff b)

private theorem at_bit {I : Type} (a : Aff (Option I)) (x : I → Bool) (b : Bool) :
    a.eval (extend b x) = xor (a.eval (extend false x)) (firstCoeff a && b) := by
  induction a with
  | bit j => cases j <;> cases b <;> simp [Aff.eval, extend, firstCoeff]
  | lit c => cases c <;> simp [Aff.eval, firstCoeff]
  | add p q hp hq =>
    simp only [Aff.eval, firstCoeff]
    rw [hp, hq]
    cases p.eval (extend false x) <;> cases q.eval (extend false x) <;>
      cases firstCoeff p <;> cases firstCoeff q <;> cases b <;> decide

private def plug {I : Type} (a : Aff (Option I)) (r : Aff I) := a.subst (extend r Aff.bit)

private theorem eval_plug {I : Type} (a : Aff (Option I)) (r : Aff I) (x : I → Bool) :
    (plug a r).eval x = a.eval (extend (r.eval x) x) := by
  rw [plug, Aff.eval_subst]
  congr 1
  funext j
  cases j <;> rfl

private theorem eliminate_one {I : Type} (eqs : List (Aff (Option I))) :
    ∃ new : List (Aff I), new.length ≤ eqs.length ∧
      ∀ x, Flat new x ↔ ∃ b, Flat eqs (extend b x) := by
  have choice : ∃ r : Aff I, ∀ (x : I → Bool) b,
      Flat eqs (extend b x) → Flat eqs (extend (r.eval x) x) := by
    by_cases pivot : ∃ a ∈ eqs, firstCoeff a = true
    · obtain ⟨a, ha, one⟩ := pivot
      refine ⟨plug a (.lit false), ?_⟩
      intro x b hb
      have hz := hb a ha
      rw [at_bit a x b, one, Bool.true_and] at hz
      have chosen : a.eval (extend false x) = b := by
        cases he : a.eval (extend false x) <;> cases b <;> simp_all
      simpa only [eval_plug, Aff.eval, chosen] using hb
    · refine ⟨.lit false, ?_⟩
      intro x b hb a ha
      have zero : firstCoeff a = false := by
        cases h : firstCoeff a
        · rfl
        · exact False.elim (pivot ⟨a, ha, h⟩)
      have eq := hb a ha
      rw [at_bit a x b, zero] at eq
      simpa [Aff.eval] using eq
  obtain ⟨r, sound⟩ := choice
  refine ⟨eqs.map (fun a => plug a r), by simp, ?_⟩
  intro x
  have equivalence : Flat (eqs.map (fun a => plug a r)) x ↔ Flat eqs (extend (r.eval x) x) := by
    simp [Flat, eval_plug]
  rw [equivalence]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨b, h⟩ => sound x b h⟩

/-- Add any finite number of separate witness coordinates above the public coordinates. -/
def WithAux (I : Type) : Nat → Type
  | 0 => I
  | n + 1 => Option (WithAux I n)

def publicPart {I : Type} : (n : Nat) → (WithAux I n → Bool) → I → Bool
  | 0, x => x
  | n + 1, x => publicPart n (fun j => x (some j))

/-- Exact existential projection of an affine flat through arbitrarily many
Boolean coordinates. No additional defining equations are needed. -/
theorem project_equations {I : Type} (n : Nat) (eqs : List (Aff (WithAux I n))) :
    ∃ publicEqs : List (Aff I), publicEqs.length ≤ eqs.length ∧
      ∀ x, Flat publicEqs x ↔ ∃ y, publicPart n y = x ∧ Flat eqs y := by
  induction n with
  | zero =>
    exact ⟨eqs, Nat.le_refl _, fun x =>
      ⟨fun hx => ⟨x, rfl, hx⟩, fun ⟨_, h, hy⟩ => h ▸ hy⟩⟩
  | succ n ih =>
    obtain ⟨inner, size, step⟩ := eliminate_one eqs
    obtain ⟨outer, bound, proj⟩ := ih inner
    refine ⟨outer, Nat.le_trans bound size, ?_⟩
    intro x
    rw [proj]
    constructor
    · rintro ⟨y, name, hy⟩
      obtain ⟨b, hb⟩ := (step y).mp hy
      exact ⟨extend b y, name, hb⟩
    · rintro ⟨y, name, hy⟩
      refine ⟨(fun j => y (some j)), name, (step _).mpr ⟨y none, ?_⟩⟩
      have eta : extend (y none) (fun j => y (some j)) = y := by
        funext j
        cases j <;> rfl
      rwa [eta]

/-- Two honest lifts give a common public accepting flat cut out by at most
s+1 affine public equations. Each public point on it has a witness (the
witness need not be common to different public points). -/
theorem existential_output_flat {I J : Type} (n : Nat) (p : Program (WithAux I n) J)
    (out : Aff J) (u v : WithAux I n → Bool) (c : Bool)
    (hu : out.eval (p.run u) = c) (hv : out.eval (p.run v) = c) :
    ∃ eqs : List (Aff I), eqs.length ≤ p.ands + 1 ∧
      Flat eqs (publicPart n u) ∧ Flat eqs (publicPart n v) ∧
      ∀ x, Flat eqs x → ∃ y, publicPart n y = x ∧ out.eval (p.run y) = c := by
  obtain ⟨full, bound, left, right, sound⟩ := constant_output_flat p out u v c hu hv
  obtain ⟨eqs, size, proj⟩ := project_equations n full
  refine ⟨eqs, Nat.le_trans size bound, (proj _).mpr ⟨u, rfl, left⟩,
    (proj _).mpr ⟨v, rfl, right⟩, ?_⟩
  intro x hx
  obtain ⟨y, hxy, holds⟩ := (proj x).mp hx
  exact ⟨y, hxy, sound y holds⟩

end TwoPointGateRestriction
