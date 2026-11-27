import Std

namespace LinearVerdictPivots

def Word : Nat → Type
  | 0 => Unit
  | k+1 => Bool × Word k

def zero : (k : Nat) → Word k
  | 0 => ()
  | k+1 => (false, zero k)

def plus : (k : Nat) → Word k → Word k → Word k
  | 0, _, _ => ()
  | k+1, (a, u), (b, v) => (xor a b, plus k u v)

def dot : (k : Nat) → Word k → Word k → Bool
  | 0, _, _ => false
  | k+1, (a, u), (b, v) => xor (a && b) (dot k u v)

theorem dot_zero (k : Nat) (c : Word k) : dot k c (zero k) = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨a,u⟩ := c
    simp [dot, zero, ih]

private theorem bit_distrib (a b c x y : Bool) :
    xor (a && xor b c) (xor x y) = xor (xor (a && b) x) (xor (a && c) y) := by
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> decide

theorem dot_plus (k : Nat) (c u v : Word k) :
    dot k c (plus k u v) = xor (dot k c u) (dot k c v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨a,w⟩ := c
    obtain ⟨b,x⟩ := u
    obtain ⟨d,y⟩ := v
    simp only [plus, dot, ih]
    exact bit_distrib _ _ _ _ _

/-- The relations can contain only the terminal and branch tests retained by
    a certificate. Algebraic derivations represent span predictions. -/
inductive Derives {k : Nat} (terminal : Word k → Bool → Prop)
    (branch : Word k → Word k → Word k → Prop) : Word k → Bool → Prop
  | origin : Derives terminal branch (zero k) false
  | sum {x y a b} : Derives terminal branch x a → Derives terminal branch y b →
      Derives terminal branch (plus k x y) (xor a b)
  | leaf {x a} : terminal x a → Derives terminal branch x a
  | fork {x y z a b} : branch x y z → Derives terminal branch y a →
      Derives terminal branch z b → Derives terminal branch x (a || b)

section
variable {k : Nat} {terminal : Word k → Bool → Prop}
  {branch : Word k → Word k → Word k → Prop} (c : Word k)

def Fits (c : Word k) (terminal : Word k → Bool → Prop)
    (branch : Word k → Word k → Word k → Prop) : Prop :=
  (∀ x a, terminal x a → dot k c x = a) ∧
  (∀ x y z, branch x y z → dot k c x = (dot k c y || dot k c z))

theorem sound (hc : Fits c terminal branch) {x a} (p : Derives terminal branch x a) :
    dot k c x = a := by
  induction p with
  | origin => exact dot_zero _ _
  | sum _ _ ih₁ ih₂ => rw [dot_plus, ih₁, ih₂]
  | leaf ht => exact hc.1 _ _ ht
  | fork hb _ _ ih₁ ih₂ => rw [hc.2 _ _ _ hb, ih₁, ih₂]

theorem conflict {x} (h₀ : Derives terminal branch x false)
    (h₁ : Derives terminal branch x true) : ¬ Fits c terminal branch := by
  intro hc
  have hz := sound c hc h₀
  have ho := sound c hc h₁
  simp [hz] at ho

end

def sumRows (k : Nat) : List (Word k) → Word k
  | [] => zero k
  | x :: xs => plus k x (sumRows k xs)

/-- If a true terminal's tuple is an XOR of tuples which every exact
    selector must reject, that selector cannot give the terminal value one. -/
theorem challenge_excludes {k : Nat} (c t : Word k) (queries : List (Word k))
    (dep : t = sumRows k queries) (reject : ∀ x ∈ queries, dot k c x = false) :
    dot k c t ≠ true := by
  have vanishes : ∀ xs : List (Word k),
      (∀ x ∈ xs, dot k c x = false) → dot k c (sumRows k xs) = false := by
    intro xs
    induction xs with
    | nil => intro _; exact dot_zero _ _
    | cons x xs ih =>
      intro h
      rw [sumRows, dot_plus, h x (by simp), ih (by
        intro y hy
        exact h y (by simp [hy]))]
      decide
  rw [dep, vanishes queries reject]
  decide

end LinearVerdictPivots
