import Std

namespace SharedLevinClock

/-- Both running times are logarithmic costs. -/
def shared (p v u w : Nat) : Nat := p + v + max u w

def separate (p v u w : Nat) : Nat := p + v + u + w

theorem splitTimes (u w : Nat) : max u w + min u w = u + w := by
  by_cases h : u ≤ w
  · rw [Nat.max_eq_right h, Nat.min_eq_left h, Nat.add_comm]
  · have h' : w ≤ u := by omega
    rw [Nat.max_eq_left h', Nat.min_eq_right h']

theorem separate_eq (p v u w : Nat) :
    separate p v u w = shared p v u w + min u w := by
  have ht := splitTimes u w
  unfold separate shared
  omega

/-- Convex interpolation after multiplication by the denominator b.
    This also includes the two endpoints and degeneracy at b=0. -/
theorem weightedLower (p v u w n h a b : Nat) (hab : a ≤ b)
    (single : n ≤ shared p v u w) (both : n + h ≤ separate p v u w) :
    b*n + a*h ≤ b*(p+v+max u w) + a*min u w := by
  let k := b - a
  have hb : b = a + k := by dsimp [k]; omega
  have scaledSingle := Nat.mul_le_mul_left k single
  have scaledBoth := Nat.mul_le_mul_left a both
  rw [separate_eq] at scaledBoth
  change b*n + a*h ≤ b*(shared p v u w) + a*min u w
  simp only [Nat.mul_add] at scaledBoth
  rw [hb]
  simp only [Nat.add_mul]
  omega

theorem fromIndividualBounds (p v u w n h a b : Nat) (hab : a ≤ b)
    (first : n ≤ p+u) (second : h ≤ v+w) :
    b*n + a*h ≤ b*(p+v+max u w) + a*min u w := by
  apply weightedLower p v u w n h a b hab
  · have hu := Nat.le_max_left u w
    unfold shared
    omega
  · unfold separate
    omega

/-- The equal-time example attains the two coefficients simultaneously. -/
theorem equalTimes (n a b : Nat) :
    b*(0+0+max n n) + a*min n n = b*n + a*n := by simp

/-- Each enumerated program-length bin has exactly the same total budget. -/
theorem binBudget (n l : Nat) (hl : l ≤ n) : 2^l * 2^(n-l) = 2^n := by
  rw [← Nat.pow_add, Nat.add_sub_of_le hl]

theorem binsTotal (n : Nat) (bins : List Nat) (caps : ∀ l ∈ bins, l ≤ n) :
    (bins.map (fun l => 2^l * 2^(n-l))).sum = bins.length * 2^n := by
  induction bins with
  | nil => simp
  | cons l ls ih =>
    have cap := caps l (by simp)
    have next := ih (fun z hz => caps z (by simp [hz]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    rw [binBudget n l cap, next, Nat.add_comm]

end SharedLevinClock
