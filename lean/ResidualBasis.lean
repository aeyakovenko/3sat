import Std

namespace ResidualBasis

/-- A Boolean polynomial in n variables of total degree at most d.
    The split constructor computes p(tail) + x₀ q(tail) over F₂.
    Each variable occurs at most once in each resulting monomial. -/
inductive Multilinear : Nat → Nat → Type where
  | const {n d : Nat} (value : Bool) : Multilinear n d
  | skip {n d : Nat} (p : Multilinear n d) : Multilinear (n+1) d
  | split {n d : Nat} (p : Multilinear n (d+1)) (q : Multilinear n d) :
      Multilinear (n+1) (d+1)

def eval : Multilinear n d → List Bool → Bool
  | .const v, _ => v
  | .skip p, x => eval p x.tail
  | .split p q, x => xor (eval p x.tail) (x.headD false && eval q x.tail)

/-- For a support mask a, build the sum of all monomials indexed by
    supersets of a of size at most d, by deciding the first coordinate. -/
def basis : (a : List Bool) → (d : Nat) → Multilinear a.length d
  | [], _ => .const true
  | false :: a, 0 => .skip (basis a 0)
  | true :: _, 0 => .const false
  | false :: a, d+1 => .split (basis a (d+1)) (basis a d)
  | true :: a, d+1 => .split (.const false) (basis a d)

def wt : List Bool → Nat
  | [] => 0
  | false :: tail => wt tail
  | true :: tail => wt tail + 1

private theorem cancel (u v : Bool) : xor (xor u v) v = u := by
  cases u <;> cases v <;> rfl

private theorem pair (a x : List Bool) (bit : Bool) (d : Nat) :
    xor (eval (basis (false :: a) d) (bit :: x))
        (eval (basis (true :: a) d) (bit :: x)) = eval (basis a d) x := by
  cases d with
  | zero => simp [basis, eval]
  | succ d =>
    simp [basis, eval, cancel]

/-- XOR over all masks of length n, combining siblings first. -/
def parity : Nat → (List Bool → Bool) → Bool
  | 0, f => f []
  | n+1, f => parity n (fun a => xor (f (false :: a)) (f (true :: a)))

/-- The XOR of the residuals is 1 at *every* Boolean seed. -/
theorem partition (x : List Bool) (d : Nat) :
    parity x.length (fun a => eval (basis a d) x) = true := by
  induction x with
  | nil => rfl
  | cons bit x ih =>
    simp only [List.length_cons, parity, pair]
    exact ih

/-- Supports larger than d give zero, so they can be omitted from the family. -/
theorem vanishes_above (a : List Bool) (d : Nat) (large : d < wt a)
    (x : List Bool) (len : a.length = x.length) : eval (basis a d) x = false := by
  induction a generalizing d x with
  | nil => simp [wt] at large
  | cons bit a ih =>
    cases x with
    | nil => simp at len
    | cons v x =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      cases bit <;> cases d with
      | zero => simp_all [basis, wt, eval]
      | succ d =>
        simp only [wt] at large
        simp [basis, eval, ih (d := d) (by omega) x len,
          fun h : d+1 < wt a => ih (d := d+1) h x len, *]

/-- Evaluation on Hamming weight ≤ d is the identity evaluation matrix. -/
theorem private_point (a x : List Bool) (d : Nat) (len : a.length = x.length)
    (small : wt x ≤ d) : eval (basis a d) x = decide (a = x) := by
  induction x generalizing a d with
  | nil => cases a <;> simp_all [basis, eval]
  | cons bit x ih =>
    cases a with
    | nil => simp at len
    | cons t a =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      cases bit <;> cases t <;> cases d with
      | zero => simp_all [wt, basis, eval]
      | succ d =>
        simp only [wt] at small
        simp [basis, eval, ih a (d+1) len (by omega),
          fun h : wt x ≤ d => ih a d len h, *]
        all_goals first | exact ih a d len (by omega) | exact (ih a d len (by omega)).symm

private theorem parity_witness (n : Nat) (f : List Bool → Bool) (h : parity n f = true) :
    ∃ a, a.length = n ∧ f a = true := by
  induction n generalizing f with
  | zero => exact ⟨[], rfl, h⟩
  | succ n ih =>
    obtain ⟨a, len, odd⟩ := ih (fun a => xor (f (false :: a)) (f (true :: a))) h
    by_cases left : f (false :: a) = true
    · exact ⟨false :: a, by simp [len], left⟩
    · have right : f (true :: a) = true := by
        cases hl : f (false :: a) <;> cases hr : f (true :: a) <;> simp_all
      exact ⟨true :: a, by simp [len], right⟩

/-- Every seed violates at least one of the equations indexed by weight ≤ d. -/
theorem no_common_zero (x : List Bool) (d : Nat) :
    ∃ a, a.length = x.length ∧ wt a ≤ d ∧ eval (basis a d) x = true := by
  obtain ⟨a, len, yes⟩ := parity_witness _ _ (partition x d)
  refine ⟨a, len, ?_, yes⟩
  by_cases heavy : d < wt a
  · have no := vanishes_above a d heavy x len
    simp_all
  · omega

/-- The seed a satisfies every remaining equation once its own index is removed. -/
theorem deletion_witness (a : List Bool) (d : Nat) (small : wt a ≤ d) :
    eval (basis a d) a = true ∧
    ∀ c, c.length = a.length → c ≠ a → eval (basis c d) a = false := by
  constructor
  · simp [private_point a a d rfl small]
  · intro c len ne
    simp [private_point c a d len small, ne]

end ResidualBasis
