import Std

namespace UniqueWitnessBatches

/-- Unfolding a finite XOR-AND circuit lets us prove a local invariant by
    structural induction. Shared occurrences retain the same evaluations. -/
inductive Gate (I : Type) where
  | input (i : I)
  | const (b : Bool)
  | add (a b : Gate I)
  | mul (a b : Gate I)

def val (x : I → Bool) : Gate I → Bool
  | .input i => x i
  | .const b => b
  | .add a b => xor (val x a) (val x b)
  | .mul a b => val x a && val x b

def base (g : Gate I) := val (fun _ => false) g

def tangent (x : I → Bool) : Gate I → Bool
  | .input i => x i
  | .const _ => false
  | .add a b => xor (tangent x a) (tangent x b)
  | .mul a b => xor (base a && tangent x b) (base b && tangent x a)

def clean (x : I → Bool) : Gate I → Prop
  | .input _ | .const _ => True
  | .add a b => clean x a ∧ clean x b
  | .mul a b => clean x a ∧ clean x b ∧ (tangent x a = false ∨ tangent x b = false)

private theorem addStep (a b c d : Bool) :
    xor (xor a c) (xor b d) = xor (xor a b) (xor c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem productStep (a b da db : Bool) (kill : da = false ∨ db = false) :
    ((xor a da) && (xor b db)) = xor (a && b) (xor (a && db) (b && da)) := by
  cases a <;> cases b <;> cases da <;> cases db <;> simp_all

theorem exactOnKernel (x : I → Bool) (g : Gate I) (h : clean x g) :
    val x g = xor (base g) (tangent x g) := by
  induction g with
  | input i => simp [val, base, tangent]
  | const b => simp [val, base, tangent]
  | add a b ha hb =>
    obtain ⟨ca,cb⟩ := h
    change xor (val x a) (val x b) = xor (xor (base a) (base b)) (xor (tangent x a) (tangent x b))
    rw [ha ca, hb cb]
    exact addStep _ _ _ _
  | mul a b ha hb =>
    obtain ⟨ca,cb,k⟩ := h
    change (val x a && val x b) = xor (base a && base b)
      (xor (base a && tangent x b) (base b && tangent x a))
    rw [ha ca, hb cb]
    exact productStep _ _ _ _ k

theorem repeatedInput : val (fun _ : Unit => true) (.mul (.input ()) (.input ())) = true ∧
    tangent (fun _ : Unit => true) (.mul (.input ()) (.input ())) = false := by decide

/-- Finite Boolean vectors without external linear-algebra dependencies. -/
def Vec : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Vec n

def zero : (n : Nat) → Vec n
  | 0 => ()
  | n+1 => (false, zero n)

def plus : (n : Nat) → Vec n → Vec n → Vec n
  | 0, _, _ => ()
  | n+1, (b,u), (c,v) => (xor b c, plus n u v)

def dot : (n : Nat) → Vec n → Vec n → Bool
  | 0, _, _ => false
  | n+1, (b,u), (c,v) => xor (b && c) (dot n u v)

private theorem selfPlus (n : Nat) (u : Vec n) : plus n u u = zero n := by
  induction n with
  | zero => rfl
  | succ n ih => obtain ⟨b,v⟩ := u; simp [plus, zero, ih]

private theorem zeroPlus (n : Nat) (u : Vec n) : plus n (zero n) u = u := by
  induction n with
  | zero => cases u; rfl
  | succ n ih => obtain ⟨b,v⟩ := u; simp [plus, zero, ih]

private theorem linearIsDot (n : Nat) (f : Vec n → Bool)
    (lin : ∀ u v, f (plus n u v) = xor (f u) (f v)) :
    ∃ c, ∀ u, f u = dot n c u := by
  induction n with
  | zero =>
    have hz := lin () ()
    simp only [plus, Bool.xor_self] at hz
    exact ⟨(), fun _ => hz⟩
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih (fun v => f (false,v)) (fun v w => lin (false,v) (false,w))
    refine ⟨(f (true,zero n),c), ?_⟩
    rintro ⟨b,v⟩
    cases b with
    | false => simpa [dot] using hc v
    | true =>
      have h := lin (true,zero n) (false,v)
      simpa [plus, zeroPlus, dot, hc v] using h

/-- If independent measurements cover all syndrome vectors, every linear
    residual vanishing on their joint kernel is the parity of a subset of
    the measurements. The section can be any choice of preimages. -/
theorem correctionInSpan {X : Type} (combine : X → X → X) (k : Nat) (A : X → Vec k)
    (addA : ∀ x y, A (combine x y) = plus k (A x) (A y))
    (sectionMap : Vec k → X) (onto : ∀ v, A (sectionMap v) = v)
    (f : X → Bool) (lin : ∀ x y, f (combine x y) = xor (f x) (f y))
    (kernel : ∀ x, A x = zero k → f x = false) :
    ∃ c, ∀ x, f x = dot k c (A x) := by
  have fibers : ∀ x y, A x = A y → f x = f y := by
    intro x y he
    have hz := kernel (combine x y) (by rw [addA, he, selfPlus])
    rw [lin] at hz
    cases h : f x <;> cases q : f y <;> simp_all
  obtain ⟨c,hc⟩ := linearIsDot k (fun v => f (sectionMap v)) (by
    intro v w
    rw [← lin]
    apply fibers
    rw [addA, onto, onto, onto])
  exact ⟨c,fun x => (fibers x (sectionMap (A x)) (onto _).symm).trans (hc _)⟩

end UniqueWitnessBatches
