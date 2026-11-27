import Std

namespace WeightedWinnerPaths

/-- A missing row contributes no mass. A surviving row contributes once
    in its color, regardless of its number of witnesses. -/
def geometricMass : List (Option Bool) → Bool → Nat
  | [], _ => 0
  | h :: xs, b =>
    (if h = some b then 3 * 4 ^ xs.length else 0) + geometricMass xs b

/-- With two random bits per position, one ticket always remains unused. -/
theorem geometric_budget (xs : List (Option Bool)) :
    geometricMass xs false + geometricMass xs true + 1 ≤ 4 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons h xs ih =>
    cases h with
    | none => simp [geometricMass, Nat.pow_succ]; omega
    | some b => cases b <;> simp [geometricMass, Nat.pow_succ] <;> omega

theorem geometric_bits (n : Nat) : 4 ^ n = 2 ^ (2 * n) := by
  simp [Nat.pow_mul]

/-- Conditional mass on the least surviving row's color is at least 3/4. -/
theorem geometric_majority (b : Bool) (xs : List (Option Bool)) :
    3 * geometricMass (some b :: xs) (!b) ≤ geometricMass (some b :: xs) b := by
  have cap := geometric_budget xs
  cases b <;> simp [geometricMass] <;> omega

theorem geometric_skip (n : Nat) (xs : List (Option Bool)) (b : Bool) :
    geometricMass (List.replicate n none ++ xs) b = geometricMass xs b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, geometricMass, ih]

/-- For shared-tape threshold tests, existence of a surviving row in a
    color gives the largest threshold of that color. -/
def threshold : Nat → List (Option Bool) → Bool → Nat
  | _, [], _ => 0
  | q, h :: xs, b => if h = some b then q ^ xs.length else threshold q xs b

def hasWitness : Nat → Nat → List (Option Bool) → Bool → Prop
  | _, _, [], _ => False
  | q, ticket, h :: xs, b =>
    (h = some b ∧ ticket < q ^ xs.length) ∨ hasWitness q ticket xs b

theorem threshold_bound (q : Nat) (hq : 1 ≤ q) (xs : List (Option Bool)) (b : Bool) :
    q * threshold q xs b ≤ q ^ xs.length := by
  induction xs with
  | nil => simp [threshold]
  | cons h xs ih =>
    simp only [threshold, List.length_cons, Nat.pow_succ]
    split
    · exact Nat.le_of_eq (Nat.mul_comm _ _)
    · exact Nat.le_trans ih (by simpa using Nat.mul_le_mul_left (q ^ xs.length) hq)

theorem threshold_projects (q : Nat) (hq : 1 ≤ q) (ticket : Nat)
    (xs : List (Option Bool)) (b : Bool) :
    hasWitness q ticket xs b ↔ ticket < threshold q xs b := by
  induction xs with
  | nil => simp [hasWitness, threshold]
  | cons h xs ih =>
    simp only [hasWitness, threshold, ih]
    by_cases same : h = some b
    · have bound := threshold_bound q hq xs b
      have small : threshold q xs b ≤ q * threshold q xs b := by
        simpa using Nat.mul_le_mul_right (threshold q xs b) hq
      simpa [same] using
        (show ticket < q ^ xs.length ∨ ticket < threshold q xs b ↔ ticket < q ^ xs.length
          from ⟨fun h => h.elim id (fun h => Nat.lt_of_lt_of_le h (Nat.le_trans small bound)), Or.inl⟩)
    · simp [same]

theorem threshold_skip (q n : Nat) (xs : List (Option Bool)) (b : Bool) :
    threshold q (List.replicate n none ++ xs) b = threshold q xs b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, threshold, ih]

/-- With integer odds q, the least surviving color has at least q times
    the other color's score. The largest individual threshold is q^(L-1). -/
theorem threshold_majority (q : Nat) (hq : 1 ≤ q) (b : Bool) (xs : List (Option Bool)) :
    q * threshold q (some b :: xs) (!b) ≤ threshold q (some b :: xs) b ∧
    threshold q (some b :: xs) b = q ^ xs.length := by
  have bound := threshold_bound q hq xs (!b)
  cases b <;> simpa [threshold] using bound

/-- Along nested feasible sets both scores are nondecreasing. Whenever the
    correct color switches, accuracy u/(u+v) requires u/v-fold growth. -/
theorem alternating_growth (steps u v : Nat) (score : Nat → Bool → Nat)
    (bit : Nat → Bool)
    (mono : ∀ i, i < steps → ∀ b, score i b ≤ score (i+1) b)
    (flip : ∀ i, i < steps → bit (i+1) = !(bit i))
    (accuracy : ∀ i, i ≤ steps → u * score i (!(bit i)) ≤ v * score i (bit i)) :
    ∀ n, n ≤ steps → u ^ n * score 0 (bit 0) ≤ v ^ n * score n (bit n) := by
  intro n
  induction n with
  | zero => simp
  | succ i ih =>
    intro hi
    have before : i < steps := by omega
    have next := accuracy (i+1) hi
    rw [flip i before, Bool.not_not] at next
    rw [← flip i before] at next
    have grow := Nat.le_trans (Nat.mul_le_mul_left u (mono i before (bit i))) next
    calc
      u ^ (i+1) * score 0 (bit 0) = u * (u ^ i * score 0 (bit 0)) := by
        rw [Nat.pow_succ]; ac_rfl
      _ ≤ u * (v ^ i * score i (bit i)) := Nat.mul_le_mul_left _ (ih (by omega))
      _ = v ^ i * (u * score i (bit i)) := by ac_rfl
      _ ≤ v ^ i * (v * score (i+1) (bit (i+1))) := Nat.mul_le_mul_left _ grow
      _ = v ^ (i+1) * score (i+1) (bit (i+1)) := by rw [Nat.pow_succ]; ac_rfl

/-- The last correct score already requires one random bit per switch at
    accuracy 2/3, when each individual color has at most 2^R tapes. -/
theorem bits_for_switches (steps R last : Nat) (growth : 2 ^ steps ≤ last)
    (cap : last ≤ 2 ^ R) : steps ≤ R :=
  (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (Nat.le_trans growth cap)

/-- If the same finite tape population is partitioned into the two colors
    and both survive at the final stage, one more bit is necessary. -/
theorem bits_for_disjoint_colors (steps R last other : Nat) (growth : 2 ^ steps ≤ last)
    (positive : 0 < other) (cap : last + other ≤ 2 ^ R) : steps + 1 ≤ R := by
  have strict : 2 ^ steps < 2 ^ R := by omega
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp strict
  omega

end WeightedWinnerPaths
