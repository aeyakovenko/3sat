import Std

namespace SupportFilteredParity

/-- Number of variables absent from a monomial's exponent vector. -/
def missing : List Nat → Nat
  | [] => 0
  | 0 :: rest => missing rest + 1
  | (_ + 1) :: rest => missing rest

/-- XOR of the mask contributions. A coordinate of exponent zero may be
omitted from the mask or included if there is still room. -/
def masked : List Nat → Nat → Bool
  | [], _ => true
  | 0 :: rest, 0 => masked rest 0
  | 0 :: rest, b + 1 => masked rest (b + 1) ^^ masked rest b
  | (_ + 1) :: rest, b => masked rest b

theorem masked_full (xs : List Nat) (b : Nat) (room : missing xs ≤ b) :
    masked xs b = decide (missing xs = 0) := by
  induction xs generalizing b with
  | nil => simp [masked, missing]
  | cons e rest ih =>
    cases e with
    | zero =>
      cases b with
      | zero => simp [missing] at room
      | succ b =>
        simp only [missing] at room ⊢
        rw [masked, ih (b + 1) (by omega), ih b (by omega)]
        simp
    | succ e => exact ih b room

theorem full_has_degree (xs : List Nat) (full : missing xs = 0) :
    xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons e rest ih =>
    cases e with
    | zero => simp [missing] at full
    | succ e =>
      have bound := ih full
      simp only [List.length_cons, List.sum_cons]
      omega

def filtered (xs : List Nat) (b : Nat) : Bool :=
  if xs.length ≤ xs.sum then masked xs b else false

theorem filtered_monomial (xs : List Nat) (b : Nat)
    (room : xs.length ≤ xs.sum → missing xs ≤ b) :
    filtered xs b = decide (missing xs = 0) := by
  unfold filtered
  split
  next high => exact masked_full xs b (room high)
  next low =>
    have miss : missing xs ≠ 0 := fun h => low (full_has_degree xs h)
    simp [miss]

def xorMap (f : α → Bool) : List α → Bool
  | [] => false
  | h :: t => f h ^^ xorMap f t

theorem filter_polynomial (monomials : List (List Nat)) (b : Nat)
    (room : ∀ x ∈ monomials, x.length ≤ x.sum → missing x ≤ b) :
    xorMap (fun x => filtered x b) monomials =
      xorMap (fun x => decide (missing x = 0)) monomials := by
  induction monomials with
  | nil => rfl
  | cons x xs ih =>
    simp only [xorMap]
    rw [filtered_monomial x b (room x (by simp)),
        ih (fun y hy => room y (by simp [hy]))]

/-- Two bits give coefficients in the basis (1, α), with α²=α+1. -/
abbrev F4 := Bool × Bool

def mul (x y : F4) : F4 :=
  ((x.1 && y.1) ^^ (x.2 && y.2),
   (x.1 && y.2) ^^ (x.2 && y.1) ^^ (x.2 && y.2))

def one : F4 := (true, false)

/-- Value at α of the multilinear indicator of one bit. -/
def bitWeight : Bool → F4
  | false => (true, true)
  | true => (false, true)

theorem paired_factor (b : Bool) :
    mul (bitWeight b) (bitWeight (!b)) = one := by cases b <;> rfl

def pairedWeight : List Bool → F4
  | [] => one
  | b :: tail => mul (mul (bitWeight b) (bitWeight (!b))) (pairedWeight tail)

theorem paired_weight_one (xs : List Bool) : pairedWeight xs = one := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [pairedWeight, paired_factor, ih]; rfl

/-- Binary polynomial-basis arithmetic modulo X⁴+X³+X²+X+1. -/
def f16Step (a : Nat) : Nat :=
  if a < 8 then a * 2 else (a * 2) ^^^ 31

def f16MulAux (a b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if b % 2 = 1 then a else 0) ^^^ f16MulAux (f16Step a) (b / 2) k

def f16Mul (a b : Nat) : Nat := f16MulAux a b 4

def f16Pow (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => f16Mul a (f16Pow a k)

/-- The polynomial-basis element X has order five. Its individual powers
pass the fifth-power test, and sums of any two powers always fail. -/
theorem f16_single_double :
    (∀ i : Fin 5, f16Pow (f16Pow 2 i.val) 5 = 1) ∧
    (∀ i j : Fin 5, f16Pow (f16Pow 2 i.val ^^^ f16Pow 2 j.val) 5 ≠ 1) := by
  decide

end SupportFilteredParity
