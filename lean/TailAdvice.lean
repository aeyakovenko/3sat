import Std

namespace TailAdvice

/-- Counts the first h coordinates of a binary sequence. -/
def weight (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | h + 1 => weight p h + (if p h then 1 else 0)

theorem three_weights (p q : Nat → Bool) (h : Nat) :
    weight p h + weight q h + weight (fun j => p j ^^ q j) h ≤ 2 * h := by
  induction h with
  | zero => simp [weight]
  | succ h ih =>
    cases hp : p h <;> cases hq : q h <;>
      simp only [weight, hp, hq, Bool.false_xor, Bool.true_xor,
        Bool.not_true, Bool.not_false, if_true, Bool.false_eq_true, if_false] <;> omega

/-- In length s+2 these three nonzero codewords cannot all have weight s+1 or more. -/
theorem no_two_dependencies {s : Nat} (hs : 2 ≤ s) (p q : Nat → Bool)
    (hp : s + 1 ≤ weight p (s + 2)) (hq : s + 1 ≤ weight q (s + 2))
    (hpq : s + 1 ≤ weight (fun j => p j ^^ q j) (s + 2)) : False := by
  have bound := three_weights p q (s + 2)
  omega

/-- Doubling capacity at each advice bit still leaves at least half the tables
    uncovered when each message selects a fiber of codimension at least a+1. -/
theorem capacity {a m : Nat} (fits : a + 1 ≤ m) :
    2^a * 2^(m - (a + 1)) < 2^m := by
  rw [← Nat.pow_add]
  apply Nat.pow_lt_pow_of_lt (by decide)
  omega

end TailAdvice
