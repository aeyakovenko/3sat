import Std

namespace FirstFailureClock

/-- Extra work requested on the unique file with index `t`. -/
def pulseWork (size : Nat → Nat) (pulse : Nat → Bool) (k t : Nat) : Nat :=
  if pulse t then (size t + 1) ^ (k + 1) else (size t + 1) ^ k

/-- A finite set of slow indices can be absorbed in a private multiplier.
    Unbounded pulse indices defeat all multipliers. -/
theorem private_clock_iff_bounded_pulses (size : Nat → Nat) (pulse : Nat → Bool)
    (k : Nat) (grows : ∀ t, t ≤ size t)
    (monotone : ∀ a b, a ≤ b → size a ≤ size b) :
    (∃ C, ∀ t, pulseWork size pulse k t ≤ C * (size t + 1) ^ k) ↔
      (∃ b, ∀ t, pulse t = true → t ≤ b) := by
  constructor
  · rintro ⟨C, clock⟩
    refine ⟨C, ?_⟩
    intro t hp
    have bound := clock t
    simp only [pulseWork, hp, ↓reduceIte, Nat.pow_succ] at bound
    rw [Nat.mul_comm ((size t + 1) ^ k) (size t + 1)] at bound
    have h := Nat.le_of_mul_le_mul_right bound (Nat.pow_pos (Nat.zero_lt_succ _))
    have ht := grows t
    omega
  · rintro ⟨b, cut⟩
    refine ⟨size b + 1, ?_⟩
    intro t
    cases hp : pulse t with
    | false =>
      simpa [pulseWork, hp] using
        (Nat.le_mul_of_pos_left ((size t + 1) ^ k) (Nat.zero_lt_succ (size b)))
    | true =>
      have h := Nat.succ_le_succ (monotone t b (cut t hp))
      simpa [pulseWork, hp, Nat.pow_succ, Nat.mul_comm ((size t + 1) ^ k)] using
        Nat.mul_le_mul_right ((size t + 1) ^ k) h

/-- Delaying only at the displaced halting time singles out exactly one index. -/
theorem displaced_halt (offset t firstHalt : Nat) :
    (offset ≤ t ∧ t - offset = firstHalt) ↔ t = offset + firstHalt := by omega

end FirstFailureClock
