import Std

namespace HiddenReadCorrelation

/-- Integer-valued arrays on binary cubes, recursively split at one coordinate. -/
def Table : Nat → Type
  | 0 => Int
  | n + 1 => Table n × Table n

def combine (op : Int → Int → Int) : (n : Nat) → Table n → Table n → Table n
  | 0, a, b => op a b
  | n + 1, a, b => (combine op n a.1 b.1, combine op n a.2 b.2)

def energy : (n : Nat) → Table n → Int
  | 0, a => Int.mul a a
  | n + 1, a => energy n a.1 + energy n a.2

def walsh : (n : Nat) → Table n → Table n
  | 0, a => a
  | n + 1, a =>
    let left := walsh n a.1
    let right := walsh n a.2
    (combine (· + ·) n left right, combine (· - ·) n left right)

private theorem butterfly (u v : Int) :
    (u + v)*(u + v) + (u-v)*(u-v) = 2*(u*u + v*v) := by
  simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub]
  omega

theorem pair_energy (n : Nat) (a b : Table n) :
    energy n (combine (· + ·) n a b) + energy n (combine (· - ·) n a b) =
      2*(energy n a + energy n b) := by
  induction n with
  | zero => exact butterfly a b
  | succ n ih =>
    have left := ih a.1 b.1
    have right := ih a.2 b.2
    simp only [combine, energy] at *
    omega

theorem parseval (n : Nat) (a : Table n) :
    energy n (walsh n a) = (2:Int)^n * energy n a := by
  induction n with
  | zero => simp [walsh, energy]
  | succ n ih =>
    change energy n (combine (· + ·) n _ _) + energy n (combine (· - ·) n _ _) = _
    rw [pair_energy, ih, ih, Int.pow_succ]
    change _ = _ * (energy n a.1 + energy n a.2)
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_left_comm (2 : Int)]

def sign (b : Bool) : Int := if b then -1 else 1

/-- The four contributions from one quadratic two-bit block. -/
def pairCoeff (a b : Bool) : Int :=
    1 + sign a + sign b - sign (a ^^ b)

theorem pairCoeff_eval (a b : Bool) : pairCoeff a b = 2 * sign (a && b) := by
  cases a <;> cases b <;> decide

def quadraticCoeff : List (Bool × Bool) → Int
  | [] => 1
  | (a,b)::tail => pairCoeff a b * quadraticCoeff tail

theorem quadratic_square (xs : List (Bool × Bool)) :
    quadraticCoeff xs * quadraticCoeff xs = (4:Int)^xs.length := by
  induction xs with
  | nil => decide
  | cons ab tail ih =>
    obtain ⟨a,b⟩ := ab
    have localSq : pairCoeff a b * pairCoeff a b = 4 := by
      cases a <;> cases b <;> decide
    change (pairCoeff a b * quadraticCoeff tail) * (pairCoeff a b * quadraticCoeff tail) =
      (4:Int)^(tail.length+1)
    calc
      _ = (pairCoeff a b * pairCoeff a b) * (quadraticCoeff tail * quadraticCoeff tail) := by
        ac_rfl
      _ = _ := by rw [localSq, ih, Int.pow_succ, Int.mul_comm]


inductive Train (Q R : Type) where
  | leaf (result : R)
  | ask (question : Q) (yes no : Train Q R)

def observed (f : Q → Bool) : Train Q R → List Q
  | .leaf _ => []
  | .ask q yes no => q :: (if f q then observed f yes else observed f no)

def result (f : Q → Bool) : Train Q R → R
  | .leaf a => a
  | .ask q yes no => if f q then result f yes else result f no

/-- Agreement on the questions of one adaptive transcript preserves its conclusion. -/
theorem transcript (tree : Train Q R) (f g : Q → Bool)
    (same : ∀ q ∈ observed f tree, f q = g q) : result f tree = result g tree := by
  induction tree with
  | leaf a => rfl
  | ask q yes no iy ino =>
    have atQ := same q (by simp [observed])
    cases h : f q with
    | true =>
      have hg : g q = true := atQ.symm.trans h
      simpa [result, h, hg] using iy (fun z hz => same z (by simp [observed, h, hz]))
    | false =>
      have hg : g q = false := atQ.symm.trans h
      simpa [result, h, hg] using ino (fun z hz => same z (by simp [observed, h, hz]))

end HiddenReadCorrelation
