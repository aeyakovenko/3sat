import Std

namespace NativeTreewidthTrade

/-- Positive rational pairs are kept unreduced. The three fixed parameters
    are the numerator and denominator of c, d, and the width weight λ. -/
def treeStep (C K D V U W : Nat) (e : Nat × Nat) : Nat × Nat :=
  (C * W * D * e.1,
   K * ((W-U)*D*e.1 + U*V*e.1 + U*D*e.2))

/-- For a host with α=P/Q the new exponent is a / (1/a + α/e). -/
def hostStep (A B P Q : Nat) (e : Nat × Nat) : Nat × Nat :=
  (A*A*Q*e.1, B*(B*Q*e.1 + A*P*e.2))

def iterate (step : Nat × Nat → Nat × Nat) (start : Nat × Nat) : Nat → Nat × Nat
  | 0 => start
  | n+1 => step (iterate step start n)

def firstBelow (step : Nat × Nat → Nat × Nat) (start : Nat × Nat) (n : Nat) : Bool :=
  let values := iterate step start
  (List.range n).all (fun i => (values i).1 ≥ (values i).2) &&
    ((values n).1 < (values n).2)

theorem unitWeight : firstBelow (treeStep 8 5 8 5 1 1) (8,5) 5 = true := by decide
theorem threeFifths : firstBelow (treeStep 7 5 7 5 3 5) (7,5) 3 = true := by decide
theorem oneQuarter : firstBelow (treeStep 6 5 6 5 1 4) (6,5) 2 = true := by decide
theorem linearHost : firstBelow (hostStep 32 25 1 2) (32,25) 6 = true := by decide
theorem planarHost : firstBelow (hostStep 59 50 1 3) (59,50) 5 = true := by decide

/-- At d=e=1 the unrestricted linear-run envelope c=1+λ gives one exactly. -/
theorem neutral (u v : Nat) (valid : u ≤ v) :
    let z := treeStep (v+u) v 1 1 u v (1,1)
    z.1 = z.2 := by
  simp only [treeStep, Nat.mul_one]
  have equal : v-u+u+u = v+u := by omega
  rw [equal, Nat.mul_comm]

end NativeTreewidthTrade
