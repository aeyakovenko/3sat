import Std

namespace XorButterflies

/-- Words carry their dimension, including the one-point empty cube. -/
def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

def xorWord : (n : Nat) → Word n → Word n → Word n
  | 0, _, _ => ()
  | n+1, (a,x), (b,y) => (a ^^ b, xorWord n x y)

def cubeSum : (n : Nat) → (Word n → Int) → Int
  | 0, f => f ()
  | n+1, f => cubeSum n (fun x => f (false,x)) + cubeSum n (fun x => f (true,x))

/-- Direct sum over every possible left summand. -/
def convolution (n : Nat) (f g : Word n → Int) (z : Word n) : Int :=
  cubeSum n (fun x => f x * g (xorWord n z x))

/-- A Walsh butterfly combines the two half-transforms by a sum and a difference. -/
def walsh : (n : Nat) → (Word n → Int) → Word n → Int
  | 0, f, x => f x
  | n+1, f, (b,z) =>
    let left := walsh n (fun x => f (false,x)) z
    let right := walsh n (fun x => f (true,x)) z
    if b then left - right else left + right

private theorem walshAdd (n : Nat) (f g : Word n → Int) (z : Word n) :
    walsh n (fun x => f x + g x) z = walsh n f z + walsh n g z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,z⟩ := z
    cases b <;> simp only [walsh, Bool.false_eq_true, ↓reduceIte, ih] <;> omega

private theorem walshSub (n : Nat) (f g : Word n → Int) (z : Word n) :
    walsh n (fun x => f x - g x) z = walsh n f z - walsh n g z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,z⟩ := z
    cases b <;> simp only [walsh, Bool.false_eq_true, ↓reduceIte, ih] <;> omega

private theorem convolutionSplit (n : Nat) (f g : Word (n+1) → Int)
    (b : Bool) (z : Word n) :
    convolution (n+1) f g (b,z) =
      convolution n (fun x => f (false,x)) (fun x => g (b,x)) z +
      convolution n (fun x => f (true,x)) (fun x => g (!b,x)) z := by
  cases b <;> rfl

theorem transformConvolution (n : Nat) (f g : Word n → Int) (z : Word n) :
    walsh n (convolution n f g) z = walsh n f z * walsh n g z := by
  induction n with
  | zero => cases z; rfl
  | succ n ih =>
    obtain ⟨b,z⟩ := z
    cases b <;>
      simp only [walsh, Bool.false_eq_true, ↓reduceIte, convolutionSplit,
        Bool.not_false, Bool.not_true, walshAdd, ih, Int.add_mul, Int.mul_add,
        Int.sub_mul, Int.mul_sub] <;> omega

/-- No field inverses are needed. Each coordinate doubles the scale of
    two consecutive transforms. -/
theorem doubleTransform (n : Nat) (f : Word n → Int) (z : Word n) :
    walsh n (walsh n f) z = (2:Int)^n * f z := by
  induction n with
  | zero => simp [walsh]
  | succ n ih =>
    obtain ⟨b,z⟩ := z
    cases b <;>
      simp only [walsh, Bool.false_eq_true, ↓reduceIte, walshAdd, walshSub, ih,
        Int.pow_succ, Int.mul_right_comm ((2:Int)^n) 2] <;> omega

/-- Exact recovery of every integer convolution count after multiplication
    of the two spectra. In particular the output is divisible by 2^n. -/
theorem inverseProduct (n : Nat) (f g : Word n → Int) (z : Word n) :
    walsh n (fun x => walsh n f x * walsh n g x) z =
      (2:Int)^n * convolution n f g z := by
  have spectra : (fun x => walsh n f x * walsh n g x) =
      walsh n (convolution n f g) := funext fun x => (transformConvolution n f g x).symm
  rw [spectra, doubleTransform]

/-- A shared evaluation computes both half-tables once. Each pair of
    entries supplies one addition and one subtraction. -/
def butterflyAdditions : Nat → Nat
  | 0 => 0
  | n+1 => 2 * butterflyAdditions n + 2 * 2^n

theorem fullTableAdditions (n : Nat) : butterflyAdditions n = n * 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [butterflyAdditions, ih, Nat.succ_mul, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm 2, Nat.mul_right_comm n 2]

end XorButterflies
