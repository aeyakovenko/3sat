import Std

namespace PrefixScanCorners

abbrev Vector := Nat → Bool

def plus (a b : Vector) : Vector := fun i => a i ^^ b i

def dot : Nat → Vector → Vector → Bool
  | 0, _, _ => false
  | n + 1, a, b => dot n a b ^^ (a n && b n)

theorem four_dots (n : Nat) (a a' b b' : Vector) :
    ((dot n a b ^^ dot n a b') ^^ (dot n a' b ^^ dot n a' b')) =
      dot n (plus a a') (plus b b') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [dot, ← ih, plus]
    bv_decide

def value (n : Nat) (left right : Vector → Bool) (a b : Vector) : Bool :=
  left a ^^ right b ^^ dot n a b

/-- Arbitrary one-party terms disappear from the four corners of a zero rectangle. -/
theorem zero_rectangle {n : Nat} {left right : Vector → Bool} {a a' b b' : Vector}
    (h₀ : value n left right a b = false)
    (h₁ : value n left right a b' = false)
    (h₂ : value n left right a' b = false)
    (h₃ : value n left right a' b' = false) :
    dot n (plus a a') (plus b b') = false := by
  rw [← four_dots n a a' b b']
  simp only [value] at h₀ h₁ h₂ h₃
  bv_decide

def yParity : List (Bool × Bool) → Bool
  | [] => false
  | (_, y) :: rest => y ^^ yParity rest

/-- The first x contributes its product with every y in this suffix. -/
def triangleSum : List (Bool × Bool) → Bool
  | [] => false
  | (x, y) :: rest => (x && (y ^^ yParity rest)) ^^ triangleSum rest

def scan : List (Bool × Bool) → Bool → Bool → Bool
  | [], _, acc => acc
  | (x, y) :: rest, priorX, acc =>
    scan rest (priorX ^^ x) (acc ^^ ((priorX ^^ x) && y))

theorem scan_correct (items : List (Bool × Bool)) (priorX acc : Bool) :
    scan items priorX acc = ((acc ^^ (priorX && yParity items)) ^^ triangleSum items) := by
  induction items generalizing priorX acc with
  | nil => cases acc <;> cases priorX <;> rfl
  | cons item rest ih =>
    rcases item with ⟨x, y⟩
    simp only [scan, ih, yParity, triangleSum]
    bv_decide

end PrefixScanCorners
