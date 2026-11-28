import Std

namespace FibonacciProductPairs

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

private theorem fibNext (n : Nat) : fib (n+2) = fib n + fib (n+1) := rfl

private theorem fibPositive (n : Nat) : 0 < fib (n+1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [fibNext]; omega

private theorem fibStrict (n : Nat) : fib (n+2) < fib (n+3) := by
  rw [fibNext (n+1)]
  change fib (n+2) < fib (n+1) + fib (n+2)
  have := fibPositive n
  omega

private theorem consecutive (n : Nat) : fib n = fib (n+1) ↔ n = 1 := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      change fib (n+2) = fib (n+3) ↔ n+2 = 1
      have := fibStrict n
      omega

/-- Signed gap starting from the pair of indices (3,3). -/
private def gap (a b : Nat) : Int :=
  (fib (a+b+6) : Int) - 2 * (fib (a+3) : Int) * (fib (b+3) : Int)

private theorem gapSymm (a b : Nat) : gap a b = gap b a := by
  unfold gap
  rw [Nat.add_comm a b]
  simp only [Int.mul_assoc, Int.mul_comm (fib (a+3) : Int) (fib (b+3) : Int)]

private theorem gapStep (a b : Nat) : gap a (b+2) = gap a b + gap a (b+1) := by
  have h : a + (b+2) + 6 = (a+b+6)+2 := by omega
  have h' : a + (b+1) + 6 = (a+b+6)+1 := by omega
  unfold gap
  rw [h, h', fibNext (a+b+6), fibNext (b+3)]
  rw [show b+1+3 = b+3+1 by omega]
  simp only [Int.natCast_add, Int.mul_add]
  omega

private theorem positiveTail (f : Nat → Int)
    (step : ∀ k, f (k+2) = f k + f (k+1)) (first : 0 ≤ f 0) (second : 0 < f 1)
    (n : Nat) : 0 < f (n+1) := by
  suffices 0 ≤ f n ∧ 0 < f (n+1) from this.2
  induction n with
  | zero => exact ⟨first, second⟩
  | succ n ih => rw [step n]; omega

/-- The two-by-two initial block is 0,1;1,3. Fibonacci recurrence in each direction
propagates strict positivity to every other point in the quadrant. -/
private theorem gapZero (a b : Nat) : gap a b = 0 ↔ a = 0 ∧ b = 0 := by
  have row0 (k : Nat) : 0 < gap 0 (k+1) := positiveTail _ (gapStep 0) (by decide) (by decide) k
  have row1 (k : Nat) : 0 < gap 1 (k+1) := positiveTail _ (gapStep 1) (by decide) (by decide) k
  cases a with
  | zero =>
    cases b with
    | zero => decide
    | succ b => have := row0 b; omega
  | succ a =>
    have h0 : 0 < gap (a+1) 0 := by rw [gapSymm]; exact row0 a
    have h1 : 0 < gap (a+1) 1 := by rw [gapSymm]; exact row1 a
    cases b with
    | zero => omega
    | succ b => have := positiveTail _ (gapStep (a+1)) (Int.le_of_lt h0) h1 b; omega

private theorem atOne (v : Nat) (pos : 0 < v) : 2*fib 1*fib v = fib (1+v) ↔ v = 2 := by
  cases v with
  | zero => omega
  | succ n =>
    rw [show fib 1 = 1 by rfl, show 1+(n+1) = n+2 by omega, fibNext n]
    have := consecutive n
    omega

private theorem atTwo (v : Nat) : 2*fib 2*fib v = fib (2+v) ↔ v = 1 := by
  rw [show fib 2 = 1 by rfl, show 2+v = v+2 by omega, fibNext v]
  have := consecutive v
  omega

private theorem bigPair (a b : Nat) :
    2*fib (a+3)*fib (b+3) = fib ((a+3)+(b+3)) ↔ a = 0 ∧ b = 0 := by
  rw [← gapZero]
  unfold gap
  rw [show (a+3)+(b+3) = a+b+6 by omega]
  constructor
  · intro h
    have hc := congrArg (fun n : Nat => (n : Int)) h
    simp only [Int.natCast_mul, Int.cast_ofNat_Int] at hc
    omega
  · intro h
    have h' : (↑(2*fib (a+3)*fib (b+3)) : Int) = (↑(fib (a+b+6)) : Int) := by
      simp only [Int.natCast_mul, Int.cast_ofNat_Int]
      omega
    omega

/-- The only positive pairs satisfying the Fibonacci product equation. -/
theorem classify (u v : Nat) (hu : 0 < u) (hv : 0 < v) :
    2*fib u*fib v = fib (u+v) ↔
      (u=1 ∧ v=2) ∨ (u=2 ∧ v=1) ∨ (u=3 ∧ v=3) := by
  have swap (i j : Nat) : (2*fib i*fib j = fib (i+j)) ↔ (2*fib j*fib i = fib (j+i)) := by
    rw [Nat.add_comm i j, Nat.mul_assoc, Nat.mul_comm (fib i) (fib j), ← Nat.mul_assoc]
  by_cases h : u = 1
  · subst u; rw [atOne _ hv]; omega
  by_cases h' : u = 2
  · subst u; rw [atTwo]; omega
  by_cases k : v = 1
  · subst v; rw [swap, atOne _ hu]; omega
  by_cases k' : v = 2
  · subst v; rw [swap, atTwo]; omega
  obtain ⟨a, rfl⟩ : ∃ a, u = a+3 := ⟨u-3, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, v = b+3 := ⟨v-3, by omega⟩
  rw [bigPair]
  omega

end FibonacciProductPairs
