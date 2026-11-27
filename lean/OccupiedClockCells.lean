import Std

namespace OccupiedClockCells

/-- Count the strict decreases on adjacent samples, starting with sample a. -/
def occupied (lengthAt : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => occupied lengthAt a n +
      (if lengthAt (a + n + 1) < lengthAt (a + n) then 1 else 0)

theorem decreases_consume_length (f : Nat → Nat) (a n : Nat)
    (mono : ∀ j, f (j + 1) ≤ f j) :
    f (a + n) + occupied f a n ≤ f a := by
  induction n with
  | zero => simp [occupied]
  | succ n ih =>
    have step := mono (a + n)
    by_cases h : f (a + n + 1) < f (a + n)
    · change f (a+n+1) + (occupied f a n + (if f (a+n+1) < f (a+n) then 1 else 0)) ≤ f a
      rw [if_pos h]
      omega
    · change f (a+n+1) + (occupied f a n + (if f (a+n+1) < f (a+n) then 1 else 0)) ≤ f a
      rw [if_neg h]
      omega

/-- If both endpoint comparisons come from the same plateau, only the additive
    compiler overheads can be lost in its interior. Ordinary finite lengths suffice:
    on any finite sample set infinity can also be represented by a common cap
    strictly above every finite observation. -/
theorem interior_count (f : Nat → Nat) (a n plateau c₁ c₂ : Nat)
    (mono : ∀ j, f (j + 1) ≤ f j)
    (early : f a ≤ plateau + c₂)
    (late : plateau ≤ f (a + n) + c₁) :
    occupied f a n ≤ c₁ + c₂ := by
  have count := decreases_consume_length f a n mono
  omega

theorem plateau_partition (otherOccupied interiorCap : Nat) (plateauCounts : List Nat)
    (howMany : plateauCounts.length ≤ otherOccupied + 1)
    (each : ∀ n ∈ plateauCounts, n ≤ interiorCap) :
    otherOccupied + plateauCounts.sum ≤ otherOccupied + (otherOccupied + 1) * interiorCap := by
  have bounded : ∀ (xs : List Nat), (∀ n ∈ xs, n ≤ interiorCap) →
      xs.sum ≤ xs.length * interiorCap := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro hx
      have head := hx x (by simp)
      have tail := ih (fun z hz => hx z (by simp [hz]))
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  exact Nat.add_le_add_left (Nat.le_trans (bounded plateauCounts each)
    (Nat.mul_le_mul_right interiorCap howMany)) otherOccupied

end OccupiedClockCells
