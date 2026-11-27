import Std

namespace HybridTapeExponent

/-- The requested one-pass condition for c=a/b and omega=p/q, after
    clearing denominators. The caller uses positive b and q. -/
def onePass (d p q a b : Nat) : Prop :=
  (q * (d + 1) + d * p) * a^2 < q * b * b * (d + 2)

/-- The fixed-point condition with the same convention. -/
def iterated (d p q a b : Nat) : Prop :=
  (q * (d + 1) + d * p) * a^2 < q * a * b + q * b * b * (d + 1)

theorem onePass_implies_iterated {d p q a b : Nat} (aboveOne : b ≤ a)
    (bound : onePass d p q a b) : iterated d p q a b := by
  unfold onePass at bound
  unfold iterated
  have le : q * b * b ≤ q * a * b :=
    Nat.mul_le_mul_right b (Nat.mul_le_mul_left q aboveOne)
  have sum : q * b * b * (d + 2) = q * b * b * (d + 1) + q * b * b := by
    rw [show d + 2 = (d + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
  omega

example : iterated 2 1 4 43 40 ∧ ¬ onePass 2 1 4 43 40 := by
  unfold iterated onePass
  decide
example : onePass 2 1 4 1069 1000 ∧ ¬ iterated 2 1 4 108 100 := by
  unfold iterated onePass
  decide

/-- One rational update on the unreduced numerator and denominator of e. -/
def next (d p q a b : Nat) (e : Nat × Nat) : Nat × Nat :=
  (a^2 * (q*(d+1)+d*p) * e.1, b*q * (b*(d+1)*e.1+a*e.2))

def run (d p q a b : Nat) : Nat → Nat × Nat
  | 0 => (a,b)
  | i+1 => next d p q a b (run d p q a b i)

example :
    let e := run 2 1 4 43 40
    (e 1).2 < (e 1).1 ∧ (e 3).1 < (e 3).2 := by decide

end HybridTapeExponent
