import Std

namespace NativeHistoryParity

/-- Dimensions of the free subcubes at the accepting leaves of a deterministic
test. Each free position doubles the number of indices reaching the leaf. -/
def acceptedMass : List Nat → Nat
  | [] => 0
  | d :: rest => 2 ^ d + acceptedMass rest

theorem divisible_of_leaf_dimensions (dims : List Nat) (h : Nat)
    (large : ∀ d ∈ dims, h ≤ d) :
    2 ^ h ∣ acceptedMass dims := by
  induction dims with
  | nil => exact Nat.dvd_zero _
  | cons d ds ih =>
    apply Nat.dvd_add
    · exact Nat.pow_dvd_pow 2 (large d (by simp))
    · exact ih (fun z hz => large z (by simp [hz]))

theorem touches_all_but (dims : List Nat) (h : Nat)
    (smallValuation : ¬ 2 ^ (h + 1) ∣ acceptedMass dims) :
    ∃ d ∈ dims, d ≤ h := by
  apply Classical.byContradiction
  intro absent
  apply smallValuation
  apply divisible_of_leaf_dimensions
  intro d hd
  by_cases short : d ≤ h
  · exact False.elim (absent ⟨d, hd, short⟩)
  · omega

/-- XOR of successive changes of a potential along a walk. -/
def changes (start : Bool) (interior : List Bool) (finish : Bool) : Bool :=
  match interior with
  | [] => start ^^ finish
  | y :: ys => (start ^^ y) ^^ changes y ys finish

theorem changes_endpoints (interior : List Bool) (start finish : Bool) :
    changes start interior finish = (start ^^ finish) := by
  induction interior generalizing start with
  | nil => rfl
  | cons y ys ih =>
    simp only [changes, ih]
    cases start <;> cases y <;> cases finish <;> rfl

theorem closed_changes (interior : List Bool) (start : Bool) :
    changes start interior start = false := by
  rw [changes_endpoints, Bool.xor_self]

/-- Memory indexed by inverse address, before address/word wrap. -/
def valueAfter (iterations inverseAddress : Nat) : Nat :=
  if inverseAddress < iterations then 2 * inverseAddress + 1 else 0

theorem next_write (iterations inverseAddress : Nat) :
    valueAfter (iterations + 1) inverseAddress =
      if inverseAddress = iterations then 2 * iterations + 1
      else valueAfter iterations inverseAddress := by
  by_cases hit : inverseAddress = iterations
  · subst inverseAddress
    simp [valueAfter]
  · have same : inverseAddress < iterations + 1 ↔ inverseAddress < iterations := by omega
    simp [valueAfter, hit, same]

/-- Eligible pulses are tested in priority order. -/
def firstPulse (p : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | a :: more => if p a then some a else firstPulse p more

/-- Deleting a prefix of ranks preserves the first actual eligible pulse,
provided any actual winner is outside the deleted prefix. -/
theorem omit_losers (ranks : List Nat) (p : Nat → Bool) (cut : Nat)
    (winnerKept : ∀ a, firstPulse p ranks = some a → cut ≤ a) :
    firstPulse (fun a => p a && decide (cut ≤ a)) ranks = firstPulse p ranks := by
  induction ranks with
  | nil => rfl
  | cons a tail ih =>
    cases hp : p a with
    | false =>
      simp only [firstPulse, hp, Bool.false_and, Bool.false_eq_true, if_false]
      apply ih
      intro x hx
      exact winnerKept x (by simpa [firstPulse, hp] using hx)
    | true =>
      have valid := winnerKept a (by simp [firstPulse, hp])
      simp [firstPulse, hp, valid]

end NativeHistoryParity
