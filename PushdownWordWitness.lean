import Std

namespace PushdownWordWitness

/-- Each accepting call at index j+2 contains disjoint accepting calls
    at j+1 and j. The numbers may include any intervening instructions. -/
theorem paired_call_growth (steps : Nat → Nat)
    (zero : 1 ≤ steps 0) (one : 1 ≤ steps 1)
    (recurs : ∀ j, steps j + steps (j+1) ≤ steps (j+2)) (n : Nat) :
    2^n ≤ steps (2*n) ∧ 2^n ≤ steps (2*n+1) := by
  induction n with
  | zero => exact ⟨zero, one⟩
  | succ n ih =>
    have even := recurs (2*n)
    have odd := recurs (2*n+1)
    rw [show 2*n+1+1 = 2*n+2 by omega, show 2*n+1+2 = 2*n+2+1 by omega] at odd
    simp only [Nat.mul_succ, Nat.pow_succ]
    omega

/-- The list of generated lengths, newest first, for binary straight-line
    programs. A terminal has length zero or one; a concatenation may repeat a
    previously generated child or refer to any two earlier children. -/
inductive Generated : List Nat → Prop where
  | empty : Generated []
  | terminal {xs : List Nat} (old : Generated xs) (v : Nat) (unit : v ≤ 1) :
      Generated (v :: xs)
  | concat {xs : List Nat} (old : Generated xs) (a b : Nat)
      (left : a ∈ xs) (right : b ∈ xs) : Generated ((a+b) :: xs)

theorem length_le_pow (xs : List Nat) (g : Generated xs) :
    ∀ z ∈ xs, z ≤ 2^xs.length := by
  induction g with
  | empty => simp
  | @terminal xs _ v unit ih =>
    intro z hz
    have pos : 0 < 2^xs.length := Nat.pow_pos (by decide)
    simp only [List.length_cons, Nat.pow_succ]
    rcases List.mem_cons.mp hz with rfl | h
    · omega
    · have bound := ih z h
      omega
  | @concat xs _ a b ha hb ih =>
    intro z hz
    simp only [List.length_cons, Nat.pow_succ]
    rcases List.mem_cons.mp hz with rfl | h
    · have la := ih a ha
      have lb := ih b hb
      omega
    · have bound := ih z h
      omega

theorem grammar_rules_needed {xs : List Nat} (g : Generated xs) {z b : Nat}
    (produced : z ∈ xs) (large : 2^b ≤ z) : b ≤ xs.length := by
  have bound := length_le_pow xs g z produced
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (Nat.le_trans large bound)

end PushdownWordWitness
