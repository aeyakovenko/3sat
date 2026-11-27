import Std

namespace AlternatingWitnessCertificate

/-- An unmarked position contributes no witness. A marked position carries
    the parity of its label. The returned mask names the retained positions. -/
def selection (expected : Bool) : List (Option Bool) → List Bool
  | [] => []
  | mark :: tail =>
    if mark = some expected then true :: selection (!expected) tail
    else false :: selection expected tail

/-- At a selected position the required witness must be present. At every
    skipped position a witness of the currently expected parity is forbidden. -/
inductive Replays : Bool → List (Option Bool) → List Bool → Prop where
  | nil : Replays expected [] []
  | retain (tail : Replays (!expected) marks mask) :
      Replays expected (some expected :: marks) (true :: mask)
  | skip (forbidden : mark ≠ some expected) (tail : Replays expected marks mask) :
      Replays expected (mark :: marks) (false :: mask)

theorem replay_selection (expected : Bool) (marks : List (Option Bool)) :
    Replays expected marks (selection expected marks) := by
  induction marks generalizing expected with
  | nil => exact .nil
  | cons mark rest ih =>
    by_cases h : mark = some expected
    · subst mark
      simpa [selection] using (Replays.retain (ih (!expected)))
    · simpa [selection, h] using (Replays.skip h (ih expected))

theorem replay_iff {expected : Bool} {marks : List (Option Bool)} {mask : List Bool} :
    Replays expected marks mask ↔ mask = selection expected marks := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | retain _ ih => simp [selection, ih]
    | skip h _ ih => simp [selection, h, ih]
  · rintro rfl
    exact replay_selection _ _

def count (expected : Bool) (marks : List (Option Bool)) : Nat :=
  (selection expected marks).count true

/-- After this first mark the two scans have identical expected parities.
    Arbitrarily many unmarked positions may precede it. -/
theorem first_parity_counts_one_more (p : Bool) (rest : List (Option Bool)) (blank : Nat) :
    let marks := List.replicate blank none ++ (some p :: rest)
    count p marks = count (!p) marks + 1 := by
  dsimp only
  induction blank with
  | zero => cases p <;> simp [count, selection, List.count_cons]
  | succ n ih => simpa [List.replicate_succ, count, selection, List.count_cons] using ih

/-- Specialization to any nonempty list of marked parities, of any length. -/
theorem one_more_on_nonempty_list (p : Bool) (rest : List Bool) :
    count p ((p :: rest).map some) = count (!p) ((p :: rest).map some) + 1 := by
  simpa using first_parity_counts_one_more p (rest.map some) 0

theorem exactly_one_odd_count (p : Bool) (rest : List Bool) :
    let marks := (p :: rest).map some
    (count p marks % 2 = 1) ↔ ¬ (count (!p) marks % 2 = 1) := by
  dsimp only
  have diff := one_more_on_nonempty_list p rest
  omega

/-- The certificate consists of the initial expected parity and the mask.
    The verifier checks every membership and forbidden position, then oddness. -/
def Accepts (marks : List (Option Bool)) (cert : Bool × List Bool) : Prop :=
  Replays cert.1 marks cert.2 ∧ cert.2.count true % 2 = 1

theorem unique_odd_certificate (p : Bool) (rest : List (Option Bool)) (blank : Nat) :
    let marks := List.replicate blank none ++ (some p :: rest)
    ∃ c, Accepts marks c ∧ ∀ c', Accepts marks c' → c' = c := by
  let marks := List.replicate blank none ++ (some p :: rest)
  have diff : count p marks = count (!p) marks + 1 :=
    first_parity_counts_one_more p rest blank
  have only (b : Bool) (odd : count b marks % 2 = 1) :
      ∃ c, Accepts marks c ∧ ∀ c', Accepts marks c' → c' = c := by
    refine ⟨(b, selection b marks), ⟨replay_selection _ _, odd⟩, ?_⟩
    rintro ⟨c, mask⟩ ⟨replayed, claimed⟩
    have eqmask : mask = selection c marks := replay_iff.mp replayed
    subst mask
    change count c marks % 2 = 1 at claimed
    have same : c = b := by
      cases p <;> cases b <;> cases c <;> simp_all <;> omega
    cases same
    rfl
  by_cases h : count p marks % 2 = 1
  · exact only p h
  · exact only (!p) (by omega)

theorem unmarked_rejects (k : Nat) (c : Bool × List Bool) :
    ¬ Accepts (List.replicate k none) c := by
  have noRetained : (selection c.1 (List.replicate k none)).count true = 0 := by
    induction k with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, selection, List.count_cons] using ih
  rintro ⟨replayed, odd⟩
  rw [replay_iff.mp replayed] at odd
  simp [noRetained] at odd

theorem empty_rejects (c : Bool × List Bool) : ¬ Accepts [] c := by
  rintro ⟨h, odd⟩
  have empty : c.2 = [] := replay_iff.mp h
  simp [empty] at odd

end AlternatingWitnessCertificate
