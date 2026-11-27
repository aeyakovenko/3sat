import Std

/-! Finite exponent accounting for the fixed-window negative-sign simulation.
The floor is A/S, the starting exponent is R/T, and the multiplier is C/D.
All fractions stand for nonnegative numbers with positive denominators.
The iterated numerator at depth i has denominator S*T*D^i. -/

namespace SignedSnapshotWindows

def numerator (A S C D R T : Nat) : Nat → Nat
  | 0 => R*S
  | i+1 => max (A*T*D^(i+1)) (numerator A S C D R T i*C)

theorem numerator_closed (A S C D R T i : Nat)
    (floor_le_seed : A*T ≤ R*S) (contract : C ≤ D) :
    numerator A S C D R T i = max (A*T*D^i) (R*S*C^i) := by
  induction i with
  | zero => simpa [numerator] using (Nat.max_eq_right floor_le_seed).symm
  | succ i ih =>
    rw [numerator, ih, ← Nat.mul_max_mul_right, Nat.pow_succ, Nat.pow_succ]
    have absorbs : A*T*D^i*C ≤ A*T*(D^i*D) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ contract
    rw [← Nat.max_assoc, Nat.max_eq_left absorbs]
    simp only [Nat.mul_assoc]

/-- For c=r=8/5, e=d=1/100, b=79/80, the chart charge is
249/250 and the segment multiplier is 399/400. The first strict
crossing occurs at depth 188 for the displayed rational parameters. -/
theorem negative_example :
    8*(8*400-79*25+1*20)*250 = 249*(5*2000) ∧
    79*5+1*4 = 399 ∧
    249*5 ≤ 8*250 ∧
    250*5*400^187 ≤ max (249*5*400^187) (8*250*399^187) ∧
    max (249*5*400^188) (8*250*399^188) < 250*5*400^188 := by
  decide

/-- For c=r=4/3, e=1/16, d=1/32, b=11/16, the two
positive-sign charges are 17/18 and 23/24. -/
theorem positive_example :
    4*(4*16-11*3+1*3)*18 = 17*(3*48) ∧
    4*(11*2+1)*24 = 23*(3*32) ∧ 17<18 ∧ 23<24 := by
  decide

end SignedSnapshotWindows
