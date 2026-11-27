import Std

namespace SeedFilterAdvice

/-- A list hits the sets of seeds covered by all concentrated offer programs.
Both proposed pins on each list entry are false. -/
theorem sound_program_misses_coverage
    {Code Seed Index : Type} (offer : Code → Seed → Bool → Prop)
    (truth : Seed → Bool → Bool) (dense : Code → Prop) (selected : Index → Seed)
    (hits : ∀ c, dense c → ∃ i b, offer c (selected i) b)
    (flips : ∀ i b, truth (selected i) b = !b)
    (c : Code) (sound : ∀ r b, offer c r b → truth r b = b) : ¬ dense c := by
  intro high
  obtain ⟨i, b, path⟩ := hits c high
  have wrong := flips i b
  have right := sound _ _ path
  rw [right] at wrong
  cases b <;> contradiction

/-- Counts on an equal-size expansion of the two halves of the mixture.
Matching the proposed pin differs from correctness on at most `exceptions`
uniform samples. Every list sample reverses the pin. -/
theorem mixture_correct_count {total uniformMatch listMatch uniformCorrect listCorrect
    exceptions discrepancy : Nat}
    (uniform : uniformCorrect ≤ uniformMatch + exceptions)
    (flipped : listCorrect + listMatch = total)
    (sample : uniformMatch ≤ listMatch + discrepancy) :
    uniformCorrect + listCorrect ≤ total + discrepancy + exceptions := by
  omega

/-- Deterministic gap estimates suffice to certify a list. Integer counts
use a common scaling of the true and estimated means. -/
theorem certified_discrepancy {u v approxU approxV tolerance gap : Nat}
    (left : u ≤ approxU + tolerance) (close : approxU ≤ approxV + gap)
    (right : approxV ≤ v + tolerance) : u ≤ v + gap + 2 * tolerance := by
  omega

/-- Raising feasible ranks coordinatewise cannot lower their checksum. -/
private theorem checksum_mono (rows : List (Nat × Nat))
    (raised : ∀ r ∈ rows, r.1 ≤ r.2) :
    (rows.map Prod.fst).sum ≤ (rows.map Prod.snd).sum := by
  induction rows with
  | nil => exact Nat.le_refl _
  | cons h tail ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (raised h (by simp)) (ih (fun r hr => raised r (by simp [hr])))

/-- A trusted minimum checksum certifies all the individual offer minima,
    including sentinel rows, using positive feasibility witnesses only. -/
theorem checksum_recovers_minima (rows : List (Nat × Nat))
    (raised : ∀ r ∈ rows, r.1 ≤ r.2)
    (checksum : (rows.map Prod.fst).sum = (rows.map Prod.snd).sum) :
    ∀ r ∈ rows, r.1 = r.2 := by
  induction rows with
  | nil => simp
  | cons h tail ih =>
    have head := raised h (by simp)
    have rest : ∀ r ∈ tail, r.1 ≤ r.2 := fun r hr => raised r (by simp [hr])
    have tailLe := checksum_mono tail rest
    simp only [List.map_cons, List.sum_cons] at checksum
    intro r hr
    rcases List.mem_cons.mp hr with same | member
    · subst r
      omega
    · exact ih rest (by omega) r member

end SeedFilterAdvice
