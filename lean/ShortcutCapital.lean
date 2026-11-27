import Std

namespace ShortcutCapital

/-- Costs are integral units of one common dyadic denominator. -/
structure Funds where
  abstains : Nat
  zero : Nat
  one : Nat

def before (f : Funds) := f.abstains + f.zero + f.one

def outcome (f : Funds) : Bool := decide (f.one < f.zero)

def after (f : Funds) : Nat :=
  if outcome f then f.abstains + 2 * f.one else f.abstains + 2 * f.zero

theorem budget (f : Funds) : after f ≤ before f := by
  unfold after before outcome
  by_cases h : f.one < f.zero <;> simp [h] <;> omega

/-- Abstention leaves a sound participant's stake unchanged. -/
def soundStake : List Bool → Nat → Nat
  | [], w => w
  | true :: xs, w => soundStake xs (2 * w)
  | false :: xs, w => soundStake xs w

def offers : List Bool → Nat
  | [] => 0
  | true :: xs => offers xs + 1
  | false :: xs => offers xs

theorem stake_eq (xs : List Bool) (w : Nat) :
    soundStake xs w = 2 ^ offers xs * w := by
  induction xs generalizing w with
  | nil => simp [soundStake, offers]
  | cons x xs ih =>
    cases x <;> simp [soundStake, offers, ih, Nat.pow_succ, Nat.mul_assoc]

theorem max_sound_offers (xs : List Bool) (s : Nat)
    (survives : soundStake xs 1 ≤ 2 ^ s) : offers xs ≤ s := by
  rw [stake_eq, Nat.mul_one] at survives
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp survives

end ShortcutCapital
