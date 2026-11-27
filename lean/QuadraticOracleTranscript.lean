import Std

namespace QuadraticOracleTranscript

/-- Adding coordinate i updates the two evaluation spaces. If a coordinate
    changes neither space, all later updates from that state are identical. -/
theorem thin_coordinates {S I : Type} (update : S → I → S) (dim : S → Nat)
    (rise : ∀ s i, update s i ≠ s → dim s < dim (update s i))
    (coords : List I) (initial : S) :
    ∃ keep : List I, keep.Sublist coords ∧
      keep.foldl update initial = coords.foldl update initial ∧
      keep.length + dim initial ≤ dim (coords.foldl update initial) := by
  induction coords generalizing initial with
  | nil => exact ⟨[], .slnil, rfl, by simp⟩
  | cons i is ih =>
    by_cases same : update initial i = initial
    · obtain ⟨keep, sub, outcome, bound⟩ := ih initial
      exact ⟨keep, sub.cons _, by simpa [List.foldl, same] using outcome,
        by simpa [List.foldl, same] using bound⟩
    · obtain ⟨keep, sub, outcome, bound⟩ := ih (update initial i)
      refine ⟨i :: keep, sub.cons₂ _, outcome, ?_⟩
      have h := rise initial i same
      simp only [List.length_cons, List.foldl_cons]
      omega

/-- Every reply selected by the may-query rule extends the previous
    realizability invariant, even when the point queried depends on all
    previous replies. Witnesses can change from one prefix to the next. -/
theorem feasible_trace {A : Type} (agrees : A → Nat → Prop)
    (initial : ∃ a, agrees a 0)
    (extend : ∀ i, (∃ a, agrees a i) → ∃ a, agrees a (i+1))
    (r : Nat) : ∃ a, agrees a r := by
  induction r with
  | zero => exact initial
  | succ i ih => exact extend i ih

/-- An error term can affect at most one of several calls if its
    distinguished coordinate is Boolean on every other call. -/
theorem majority_of_distinct_faults (good bad faults : Nat)
    (calls : good + bad = 2*faults+1) (one_per_fault : bad ≤ faults) :
    faults < good ∧ bad < good := by omega

end QuadraticOracleTranscript
