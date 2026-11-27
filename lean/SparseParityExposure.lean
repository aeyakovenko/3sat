import Std

namespace SparseParityExposure

/-- One permitted edit in a lower-priority selected row stays inside the
    weight limit of a higher-priority failed search. -/
theorem reserve (cap earlier later before after : Nat) (order : earlier < later)
    (room : later + 1 ≤ cap) (small : before ≤ cap - later - 1)
    (oneChange : after ≤ before + 1) : after ≤ cap - earlier - 1 := by
  omega

theorem sum_lower (counts : List Nat) (threshold : Nat)
    (each : ∀ c ∈ counts, threshold ≤ c) :
    counts.length * threshold ≤ counts.sum := by
  induction counts with
  | nil => simp
  | cons h t ih =>
    have head := each h (by simp)
    have tail := ih (fun c hc => each c (List.mem_cons_of_mem _ hc))
    simp [List.sum_cons, Nat.add_mul]
    omega

/-- Tapes counted by coordinate exposure. If aggregate exposure is smaller
    than the acceptance surplus on all positions, one flip defeats soundness.
    All counts can first be scaled by a common denominator. -/
theorem violating_flip (visits : List Nat) (accepted allowed : Nat)
    (strict : visits.sum < visits.length * (accepted - allowed))
    (changed : Nat → Nat) (couple : ∀ c ∈ visits, accepted ≤ changed c + c) :
    ∃ c ∈ visits, allowed < changed c := by
  apply Classical.byContradiction
  intro denied
  have each : ∀ c ∈ visits, accepted - allowed ≤ c := by
    intro c hc
    have h : ¬allowed < changed c := fun up => denied ⟨c, hc, up⟩
    have := couple c hc
    omega
  have bound := sum_lower visits (accepted - allowed) each
  omega

end SparseParityExposure
