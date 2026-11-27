import Std

namespace NoisyNativeEvaluation

/-- Parent merging cannot increase the number of children of a gate. -/
theorem new_children (a b same : Bool) :
    a.toNat + (b && !(a && same)).toNat ≤ a.toNat + b.toNat := by
  cases a <;> cases b <;> cases same <;> decide

/-- The integer inequality in the induction s_d ≤ 2/(d+2):
for c=d+2, (c-1)(c+1) ≤ c². -/
theorem critical_step (d : Nat) : (d+1)*(d+3) ≤ (d+2)*(d+2) := by
  simp [Nat.mul_add, Nat.add_mul]
  omega

/-- A level sample contributes only the newly completed intervals. -/
def capped (limit total : Nat) (bit : Bool) : Int :=
  if total ≤ limit then bit.toNat else 0

theorem level_difference (lo hi total : Nat) (bit : Bool) (order : lo ≤ hi) :
    capped hi total bit - capped lo total bit =
      if lo < total ∧ total ≤ hi then (bit.toNat : Int) else 0 := by
  by_cases h : total ≤ lo
  · have h' := Nat.le_trans h order
    simp [capped, h, h', Nat.not_lt_of_ge h]
  · have h' : lo < total := by omega
    by_cases k : total ≤ hi <;> simp [capped, h, k, h']

theorem telescope (start : Int) (steps : List Int) :
    (steps.foldl (· + ·) start) = start + steps.sum := by
  induction steps generalizing start with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_assoc]

end NoisyNativeEvaluation
