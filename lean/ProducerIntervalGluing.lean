import Std

/-! Three finite ingredients of the producer-block verifier. Writes at one
address are scanned in chronological order. Each nonempty candidate parent
interval is compared to other intervals at the later introduction. Supporting
records may be repeated and may be checked in any order; their labels drop
strictly from child to producer. -/

namespace ProducerIntervalGluing

/-- The most recent write at a given address strictly before the cutoff. -/
def lastWrite (write : Nat → Option W) : Nat → Option W
  | 0 => none
  | t+1 => match write t with
    | some v => some v
    | none => lastWrite write t

/-- Recover the last word even if some intervening blocks were not eligible.
It suffices that the actual latest writer is eligible. This includes the case
where the address has never been written. -/
theorem lastWriteFiltered (write : Nat → Option W) (keep : Nat → Bool)
    (t : Nat)
    (covers : ∀ j, j < t → write j ≠ none →
      (∀ u, j < u → u < t → write u = none) → keep j = true) :
    lastWrite (fun j => if keep j then write j else none) t = lastWrite write t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    cases hw : write t with
    | none =>
      have prior : ∀ j, j < t → write j ≠ none →
          (∀ u, j < u → u < t → write u = none) → keep j = true := by
        intro j hj nonempty final
        apply covers j (by omega) nonempty
        intro u hju hu
        by_cases h : u = t
        · simpa [h] using hw
        · exact final u hju (by omega)
      simp [lastWrite, hw, ih prior]
    | some v =>
      have chosen : keep t = true :=
        covers t (by omega) (by simp [hw]) (by intro u htu hu; omega)
      simp [lastWrite, hw, chosen]

theorem lastWriteAllEmpty (write : Nat → Option W) (t : Nat)
    (empty : ∀ j, j < t → write j = none) : lastWrite write t = none := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [lastWrite, empty t (by omega), ih (fun j hj => empty j (by omega))]

theorem lastWriteFromSource (write : Nat → Option W) (t p : Nat) (v : W)
    (before : p < t) (hit : write p = some v)
    (gap : ∀ j, p < j → j < t → write j = none) : lastWrite write t = some v := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hp : p = t
    · subst t
      simp [lastWrite, hit]
    · have earlier : p < t := by omega
      have empty := gap t earlier (by omega)
      simp [lastWrite, empty, ih earlier (fun j hj hu => gap j hj (by omega))]

/-- The block log names a source (or initialization), then compares separately
with each candidate producer. The comparisons determine the actual value in
the restricted candidate history. `write j = none` may also stand for an
ineligible block. -/
theorem pairChecksDetermineWord (write : Nat → Option W) (t : Nat)
    (initial value : W) (owner : Option Nat)
    (bounds : ∀ p, owner = some p → p < t)
    (atSource : ∀ p, owner = some p → write p = some value)
    (laterEmpty : ∀ p j, owner = some p → p < j → j < t → write j = none)
    (virgin : owner = none → value = initial ∧ ∀ j, j < t → write j = none) :
    (lastWrite write t).getD initial = value := by
  cases owner with
  | none =>
    obtain ⟨valueEq, empty⟩ := virgin rfl
    simp [lastWriteAllEmpty write t empty, valueEq]
  | some p =>
    have law := lastWriteFromSource write t p value (bounds p rfl) (atSource p rfl)
      (fun j hj ht => laterEmpty p j rfl hj ht)
    simp [law]

/-- An overlapping pair with distinct introduction times is tested exactly at
the later introduction, while the earlier closed interval is still live. -/
theorem overlapAtIntroduction (a b c d : Nat) (ha : a ≤ b) (hc : c ≤ d)
    (distinct : a ≠ c) :
    (∃ t, a ≤ t ∧ t ≤ b ∧ c ≤ t ∧ t ≤ d) ↔
      ((a < c ∧ c ≤ b) ∨ (c < a ∧ a ≤ d)) := by
  constructor
  · rintro ⟨t, ta, tb, tc, td⟩
    omega
  · rintro (h | h)
    · exact ⟨c, by omega, h.2, Nat.le_refl _, hc⟩
    · exact ⟨a, Nat.le_refl _, ha, by omega, h.2⟩

/-- `forces` is the local, per-parent characterization of a canonical log.
Every occurrence may discharge each parent against a different occurrence.
The existence of these witnesses follows from the check-at-coexistence and
forget-only-after-discharge rules of an accepted finite schedule. -/
theorem everyOccurrenceCanonical
    {Payload Occurrence : Type}
    (parent : Nat → Nat → Prop)
    (earlier : ∀ i j, parent i j → j < i)
    (canonical : Nat → Payload)
    (localOK : Nat → Payload → Prop)
    (pairOK : Nat → Payload → Nat → Payload → Prop)
    (forces : ∀ i v, localOK i v →
      (∀ j, parent i j → pairOK i v j (canonical j)) → v = canonical i)
    (label : Occurrence → Nat) (record : Occurrence → Payload)
    (checked : ∀ o, localOK (label o) (record o))
    (discharged : ∀ o j, parent (label o) j →
      ∃ p, label p = j ∧ pairOK (label o) (record o) j (record p)) :
    ∀ o, record o = canonical (label o) := by
  have allByLabel : ∀ n o, label o = n → record o = canonical n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n prev =>
      intro o ho
      subst n
      apply forces (label o) (record o) (checked o)
      intro j hj
      obtain ⟨p, hp, both⟩ := discharged o j hj
      have correct := prev j (earlier _ _ hj) p hp
      rw [correct] at both
      exact both
  intro o
  exact allByLabel (label o) o rfl

set_option exponentiation.threshold 2200 in
set_option maxRecDepth 6000 in
/-- Exact exponent margin in the 1024-level, two-sign transfer. The factor
(10001/10000)^2068 pays for all quantifier eliminations. -/
theorem graphProductExponentMargin :
    100 * (10001*3*1024 - 10000*1024 + 100*30000) * 10001^2068
      < 97 * (30000*1024) * 10000^2068 := by decide

end ProducerIntervalGluing
