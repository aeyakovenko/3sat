import Std

namespace DecisionTimeoutTail

variable {Input : Type}

/-- Unnormalized mass; arbitrary integer weights allow any finite rational law. -/
def mass (xs : List Input) (weight : Input → Nat) (event : Input → Bool) : Nat :=
  (xs.map (fun x => if event x then weight x else 0)).sum

def score (xs : List Input) (weight : Input → Nat) (truth : Input → Bool)
    (beforeDeadline : Input → Option Bool) (fallback : Bool) : Nat :=
  mass xs weight fun x => (beforeDeadline x).getD fallback == truth x

/-- On an early correct halt both defaults succeed, on a timeout one succeeds,
    and on an erroneous halt both fail. This holds for unbalanced truths. -/
theorem scores_identity (xs : List Input) (weight : Input → Nat) (truth : Input → Bool)
    (beforeDeadline : Input → Option Bool) :
    score xs weight truth beforeDeadline false + score xs weight truth beforeDeadline true +
      2 * mass xs weight (fun x => beforeDeadline x == some (!(truth x))) =
    mass xs weight (fun _ => true) + mass xs weight (fun x => (beforeDeadline x).isSome) := by
  induction xs with
  | nil => simp [score, mass]
  | cons x xs ih =>
    have contribution :
        (if (beforeDeadline x).getD false == truth x then weight x else 0) +
        (if (beforeDeadline x).getD true == truth x then weight x else 0) +
        2 * (if beforeDeadline x == some (!(truth x)) then weight x else 0) =
        weight x + (if (beforeDeadline x).isSome then weight x else 0) := by
      cases h : beforeDeadline x with
      | none => cases ht : truth x <;> simp
      | some b => cases b <;> cases ht : truth x <;> simp <;> omega
    simp only [score, mass, List.map_cons, List.sum_cons] at *
    simp only [if_true] at *
    omega

private theorem no_errors (xs : List Input) (weight : Input → Nat) (truth : Input → Bool)
    (early : Input → Option Bool) (correct : ∀ x b, early x = some b → b = truth x) :
    mass xs weight (fun x => early x == some (!(truth x))) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have good : (early x == some (!(truth x))) = false := by
      cases he : early x with
      | none => rfl
      | some v => have same := correct x v he; cases t : truth x <;> simp_all
    change (if early x == some (!(truth x)) then weight x else 0) + mass xs weight _ = 0
    rw [good, ih]
    rfl

/-- A correct solver halted on mass H yields a predictor scoring ≥(N+H)/2
    just by choosing between two constant timeout defaults. -/
theorem half_plus_early (xs : List Input) (weight : Input → Nat) (truth : Input → Bool)
    (early : Input → Option Bool) (correct : ∀ x b, early x = some b → b = truth x) :
    mass xs weight (fun _ => true) + mass xs weight (fun x => (early x).isSome) ≤
      2 * max (score xs weight truth early false) (score xs weight truth early true) := by
  have eq := scores_identity xs weight truth early
  rw [no_errors xs weight truth early correct] at eq
  omega

/-- A uniform upper bound on both fallback correlations gives a tail bound
    for the actual decision time. Here excess is in doubled-score units. -/
theorem early_mass_bound (xs : List Input) (weight : Input → Nat) (truth : Input → Bool)
    (early : Input → Option Bool) (correct : ∀ x b, early x = some b → b = truth x)
    (excess : Nat) (cap : ∀ b, 2 * score xs weight truth early b ≤ mass xs weight (fun _ => true) + excess) :
    mass xs weight (fun x => (early x).isSome) ≤ excess := by
  have lower := half_plus_early xs weight truth early correct
  have h0 := cap false
  have h1 := cap true
  omega

private theorem mass_union_le (xs : List Input) (weight : Input → Nat) (p q : Input → Bool) :
    mass xs weight (fun x => p x || q x) ≤ mass xs weight p + mass xs weight q := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    change (if p x || q x then weight x else 0) + mass xs weight _ ≤
      ((if p x then weight x else 0) + mass xs weight p) +
       ((if q x then weight x else 0) + mass xs weight q)
    cases hp : p x <;> cases hq : q x <;> simp <;> omega

private theorem list_cover_bound {Rank : Type} (ranks : List Rank) (xs : List Input)
    (weight : Input → Nat) (hit : Rank → Input → Bool) (cap : Nat)
    (bounded : ∀ i ∈ ranks, mass xs weight (hit i) ≤ cap) :
    mass xs weight (fun x => ranks.any (fun i => hit i x)) ≤ ranks.length * cap := by
  induction ranks with
  | nil =>
    simp only [List.any_nil, List.length_nil, Nat.zero_mul, Nat.le_zero]
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [mass] using ih
  | cons a tail ih =>
    have head := bounded a (by simp)
    have rest := ih (fun i h => bounded i (by simp [h]))
    have bound := mass_union_le xs weight (hit a) (fun x => tail.any (fun i => hit i x))
    simp only [List.any_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem best {Rank : Type} (ranks : List Rank) (nonempty : ranks ≠ []) (value : Rank → Nat) :
    ∃ i ∈ ranks, ∀ j ∈ ranks, value j ≤ value i := by
  induction ranks with
  | nil => contradiction
  | cons i tail ih =>
    by_cases e : tail = []
    · subst tail
      exact ⟨i, by simp, by simp⟩
    obtain ⟨j, member, maximal⟩ := ih e
    by_cases h : value i ≤ value j
    · refine ⟨j, by simp [member], ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | atail
      · exact h
      · exact maximal a atail
    · refine ⟨i, by simp, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | atail
      · exact Nat.le_refl _
      · exact Nat.le_trans (maximal a atail) (Nat.le_of_not_ge h)

/-- Each input can use its own favorable inner-list rank. A single fixed
    rank retains at least one list-length share of their total covered mass.
    The events for different ranks may overlap. -/
theorem one_inner_rank {Rank : Type} (ranks : List Rank) (nonempty : ranks ≠ [])
    (xs : List Input) (weight : Input → Nat) (hit : Rank → Input → Bool) :
    ∃ i ∈ ranks, mass xs weight (fun x => ranks.any (fun j => hit j x)) ≤
      ranks.length * mass xs weight (hit i) := by
  obtain ⟨i, member, maximal⟩ := best ranks nonempty (fun j => mass xs weight (hit j))
  exact ⟨i, member, list_cover_bound ranks xs weight hit _ maximal⟩

end DecisionTimeoutTail
