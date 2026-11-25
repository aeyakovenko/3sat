import Std

namespace MatrixVerifierMixedCoefficient

/-- The four coefficients of a polynomial modulo (t²,u²) in characteristic two. -/
structure Jet where
  base : Bool
  left : Bool
  right : Bool
  mixed : Bool

def Jet.add (p q : Jet) : Jet :=
  ⟨p.base ^^ q.base, p.left ^^ q.left, p.right ^^ q.right, p.mixed ^^ q.mixed⟩

def Jet.mul (p q : Jet) : Jet :=
  ⟨p.base && q.base,
   (p.base && q.left) ^^ (p.left && q.base),
   (p.base && q.right) ^^ (p.right && q.base),
   (p.base && q.mixed) ^^ (q.base && p.mixed) ^^
     (p.left && q.right) ^^ (q.left && p.right)⟩

def Jet.perturb (p : Jet) (v : Bool) : Jet :=
  { p with mixed := p.mixed ^^ v }

theorem add_perturb (p q : Jet) (v w : Bool) :
    (p.perturb v).add (q.perturb w) = (p.add q).perturb (v ^^ w) := by
  simp only [Jet.perturb, Jet.add, Jet.mk.injEq, true_and]
  bv_decide

theorem mul_perturb (p q : Jet) (v w : Bool) :
    (p.perturb v).mul (q.perturb w) =
      (p.mul q).perturb ((p.base && w) ^^ (q.base && v)) := by
  simp only [Jet.perturb, Jet.mul, Jet.mk.injEq, true_and]
  bv_decide

inductive Expr (ι : Type) where
  | literal (value : Bool)
  | input (i : ι)
  | add (a b : Expr ι)
  | mul (a b : Expr ι)

def run (inputs : ι → Jet) : Expr ι → Jet
  | .literal b => ⟨b, false, false, false⟩
  | .input i => inputs i
  | .add a b => (run inputs a).add (run inputs b)
  | .mul a b => (run inputs a).mul (run inputs b)

def directional (inputs : ι → Jet) (delta : ι → Bool) : Expr ι → Bool
  | .literal _ => false
  | .input i => delta i
  | .add a b => directional inputs delta a ^^ directional inputs delta b
  | .mul a b =>
    ((run inputs a).base && directional inputs delta b) ^^
    ((run inputs b).base && directional inputs delta a)

/-- Perturbing only the mixed input terms changes the output by the
    formal first directional derivative at the constant base. -/
theorem perturb_run (inputs : ι → Jet) (delta : ι → Bool) (g : Expr ι) :
    run (fun i => (inputs i).perturb (delta i)) g =
      (run inputs g).perturb (directional inputs delta g) := by
  induction g with
  | literal b => rfl
  | input i => rfl
  | add a b ia ib => simp only [run, directional, ia, ib, add_perturb]
  | mul a b ia ib => simp only [run, directional, ia, ib, mul_perturb]

/-- A zero output on the perturbed graph forces the unperturbed mixed
    coefficient to equal the derivative in the omitted direction (minus = plus). -/
theorem recovered_mixed (inputs : ι → Jet) (delta : ι → Bool) (g : Expr ι)
    (zero : (run (fun i => (inputs i).perturb (delta i)) g).mixed = false) :
    (run inputs g).mixed = directional inputs delta g := by
  rw [perturb_run] at zero
  change ((run inputs g).mixed ^^ directional inputs delta g) = false at zero
  bv_decide

theorem square_zero_derivative (inputs : ι → Jet) (delta : ι → Bool) (g : Expr ι) :
    directional inputs delta (.mul g g) = false := by simp [directional]

end MatrixVerifierMixedCoefficient
