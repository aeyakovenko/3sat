import Std

namespace CollisionForecast

/-- Number of set coefficients in the hidden linear form. -/
def ones : List Bool → Nat
  | [] => 0
  | false :: rest => ones rest
  | true :: rest => ones rest + 1

/-- Sum of the character over all Boolean assignments. Splitting the first
input coordinate yields equal or opposite copies of the remaining sum. -/
def characterSum : List Bool → Int
  | [] => 1
  | false :: rest => 2 * characterSum rest
  | true :: _ => 0

/-- Signed sum of offset plus assignment weight over the whole cube. -/
def weightedSum : List Bool → Int → Int
  | [], offset => offset
  | false :: rest, offset => weightedSum rest offset + weightedSum rest (offset + 1)
  | true :: rest, offset => weightedSum rest offset - weightedSum rest (offset + 1)

theorem increment (mask : List Bool) (offset : Int) :
    weightedSum mask (offset + 1) = weightedSum mask offset + characterSum mask := by
  induction mask generalizing offset with
  | nil => simp [weightedSum, characterSum]
  | cons b tail ih =>
    have first := ih offset
    have second := ih (offset + 1)
    cases b <;> simp only [weightedSum, characterSum] <;> omega

theorem character_vanishes {mask : List Bool} (nonzero : 0 < ones mask) :
    characterSum mask = 0 := by
  induction mask with
  | nil => simp [ones] at nonzero
  | cons b tail ih =>
    cases b with
    | false => simp [characterSum, ih (by simpa [ones] using nonzero)]
    | true => rfl

theorem weighted_vanishes {mask : List Bool} (two : 2 ≤ ones mask) (offset : Int) :
    weightedSum mask offset = 0 := by
  induction mask generalizing offset with
  | nil => simp [ones] at two
  | cons b tail ih =>
    cases b with
    | false =>
      have ht : 2 ≤ ones tail := by simpa [ones] using two
      simp [weightedSum, ih ht]
    | true =>
      have ht : 0 < ones tail := by simpa [ones] using two
      have step := increment tail offset
      rw [character_vanishes ht] at step
      simp [weightedSum, step]

/-- The omitted all-zero assignment had character +1 and weight -1.
Restoring nonnegative weights on the nonzero cube leaves numerator one. -/
theorem nonzero_weighted_margin {mask : List Bool} (two : 2 ≤ ones mask) :
    weightedSum mask (-1) + 1 = 1 := by
  simp [weighted_vanishes two]

end CollisionForecast
