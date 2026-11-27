import Std

namespace MatrixTriangleWalsh

inductive Word : Nat → Type
  | nil : Word 0
  | cons {n} (bit : Bool) (rest : Word n) : Word (n+1)
  deriving DecidableEq

def character : {n : Nat} → Word n → Word n → Int
  | 0, .nil, .nil => 1
  | _+1, .cons a x, .cons b y =>
      (if a && b then -1 else 1) * character x y

def total : (n : Nat) → (Word n → Int) → Int
  | 0, f => f .nil
  | n+1, f => total n (fun x => f (.cons false x)) + total n (fun x => f (.cons true x))

theorem scale (n : Nat) (c : Int) (f : Word n → Int) :
    total n (fun x => c * f x) = c * total n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih, Int.mul_add]

theorem scale_right (n : Nat) (c : Int) (f : Word n → Int) :
    total n (fun x => f x * c) = total n f * c := by
  simpa only [Int.mul_comm c] using scale n c f

theorem negate (n : Nat) (f : Word n → Int) :
    total n (fun x => -f x) = -total n f := by
  simpa using scale n (-1) f

theorem orthogonal {n} (u v : Word n) :
    total n (fun x => character x u * character x v) =
      if u = v then (2:Int)^n else 0 := by
  induction u with
  | nil => cases v; decide
  | @cons n a u ih =>
    cases v with
    | cons b v =>
      have recur := ih v
      cases a <;> cases b <;>
        simp [total, character, Int.neg_mul, Int.mul_neg, Int.neg_one_mul,
          Int.pow_succ, Word.cons.injEq, negate] at * <;>
        (first | (split <;> simp_all <;> omega) | omega)

def transformed {n : Nat} (v x y z u w : Word n) : Int :=
  total n fun i => total n fun j => total n fun k =>
    (character i v * character i x) * (character j y * character j z) *
    (character k u * character k w)

private theorem factor {n : Nat} (f g h : Word n → Int) :
    (total n fun i => total n fun j => total n fun k => f i * g j * h k) =
    total n f * total n g * total n h := by
  simp only [scale, Int.mul_assoc]
  rw [show (total n fun j => g j * total n h) = total n g * total n h
    from scale_right n _ g]
  rw [scale_right]

/-- The three transformed sign pairs have support exactly on the ordinary
matrix multiplication coefficients and share the same nonzero scale. -/
theorem transformed_triangle {n : Nat} (v x y z u w : Word n) :
    transformed v x y z u w =
      if v = x ∧ y = z ∧ u = w then (2:Int)^n * 2^n * 2^n else 0 := by
  unfold transformed
  rw [factor]
  simp only [orthogonal]
  by_cases h₁ : v=x <;> by_cases h₂ : y=z <;> by_cases h₃ : u=w <;> simp_all

end MatrixTriangleWalsh
