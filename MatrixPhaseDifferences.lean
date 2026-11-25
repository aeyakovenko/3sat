import Std

/- The parity and finite-difference identities used for one path
   of a Clifford+T circuit. Outputs are integer exponents modulo 8. -/

namespace MatrixPhaseDifferences

def bit (x : Bool) : Int := if x then 1 else 0

def thirdDiff (base a b c : Bool) : Int :=
  bit (base ^^ a ^^ b ^^ c) - bit (base ^^ a ^^ b) -
  bit (base ^^ a ^^ c) - bit (base ^^ b ^^ c) +
  bit (base ^^ a) + bit (base ^^ b) + bit (base ^^ c) - bit base

theorem affineParityThird (base a b c : Bool) :
    thirdDiff base a b c % 8 = (4 * bit a * bit b * bit c) % 8 := by
  cases base <;> cases a <;> cases b <;> cases c <;> decide

theorem inverseParityThird (base a b c : Bool) :
    (-thirdDiff base a b c) % 8 = (4 * bit a * bit b * bit c) % 8 := by
  cases base <;> cases a <;> cases b <;> cases c <;> decide

theorem evenParityThird (base a b c : Bool) :
    (2 * thirdDiff base a b c) % 8 = 0 := by
  cases base <;> cases a <;> cases b <;> cases c <;> decide

theorem sevenParities (p q r : Bool) :
    4 * bit p * bit q * bit r =
    bit p + bit q + bit r - bit (p ^^ q) - bit (p ^^ r) -
    bit (q ^^ r) + bit (p ^^ q ^^ r) := by
  cases p <;> cases q <;> cases r <;> decide

end MatrixPhaseDifferences
