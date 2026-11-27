import Std

namespace TernaryGateFaultCounts

inductive Sign where
  | zero
  | plus
  | minus
  deriving DecidableEq

def Sign.value : Sign → Int
  | .zero => 0
  | .plus => 1
  | .minus => -1

def Sign.mass : Sign → Int
  | .zero => 0
  | _ => 1

def Sign.negative : Sign → Int
  | .minus => 1
  | _ => 0

def total (weight : Sign → Int) : List Sign → Int
  | [] => 0
  | s :: rest => weight s + total weight rest

theorem count_identity (entries : List Sign) :
    total Sign.mass entries - total Sign.value entries =
      2 * total Sign.negative entries := by
  induction entries with
  | nil => decide
  | cons s rest ih =>
    cases s <;> simp only [total, Sign.mass, Sign.value, Sign.negative] <;> omega

theorem recover_bit (entries : List Sign) (bit : Int)
    (mass : total Sign.mass entries % 3 = 1)
    (inversion : total Sign.value entries % 3 = (1 - 2 * bit) % 3) :
    total Sign.negative entries % 3 = bit % 3 := by
  have identity := count_identity entries
  omega

/-- Every discarded support orbit contributes a multiple of three. -/
theorem discard_triples (fixed nonfixed count : Int) (h : count = fixed + 3 * nonfixed) :
    count % 3 = fixed % 3 := by omega

/-- Repeating a bit on an odd orbit preserves its contribution to an inner product. -/
theorem odd_multiplicity (k bit : Int) : ((2 * k + 1) * bit) % 2 = bit % 2 := by
  rw [Int.add_mul, Int.mul_assoc, Int.one_mul]
  omega

theorem fixed_parent_orbit (size : Nat)
    (positive : 0 < size) (binary : size ≤ 2)
    (orbit : size = 1 ∨ 3 ∣ size) : size = 1 := by
  rcases orbit with e | ⟨k, e⟩ <;> omega

def flip (value residual : Bool) := value ^^ residual

theorem switch_source (b residual : Bool) :
    flip (!b) residual = flip b (!residual) := by cases b <;> cases residual <;> rfl

/-- A binary AND passes a coupled disagreement precisely when its other input is one. -/
theorem pass_and (x y sibling residual : Bool) :
    (flip (x && sibling) residual ^^ flip (y && sibling) residual) =
      ((x ^^ y) && sibling) := by
  cases x <;> cases y <;> cases sibling <;> cases residual <;> rfl

end TernaryGateFaultCounts
