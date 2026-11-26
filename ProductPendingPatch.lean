import Std

namespace ProductPendingPatch

variable {ι α : Type} (predicted actual : ι → α) (pending : ι → Prop)
variable [DecidablePred pending]

def patched (i : ι) : α := if pending i then predicted i else actual i

/-- All the mismatches left after the synthetic file is decided are pointwise. -/
theorem mismatch_iff :
    predicted ≠ actual ↔ predicted ≠ patched predicted actual pending ∨
      ∃ i, pending i ∧ predicted i ≠ actual i := by
  classical
  constructor
  · intro h
    by_cases hs : predicted = patched predicted actual pending
    · right
      apply Classical.byContradiction
      intro hn
      apply h
      funext i
      by_cases hi : pending i
      · apply Classical.byContradiction
        intro hbad
        exact hn ⟨i, hi, hbad⟩
      · simpa [patched, hi] using congrFun hs i
    · exact Or.inl hs
  · rintro (hs | ⟨i, _, hi⟩) he
    · apply hs
      funext j
      simp [patched, he]
    · exact hi (congrFun he i)

/-- The same test applies to a missing operand whenever equality forces a value. -/
theorem forced_completion {β : Type} (exact : β → Prop) (x proposed : β)
    (forced : ∀ z, exact z → z = proposed) :
    ¬ exact x ↔ ¬ exact proposed ∨ x ≠ proposed := by
  classical
  constructor
  · intro h
    by_cases hx : x = proposed
    · exact Or.inl (hx ▸ h)
    · exact Or.inr hx
  · rintro (h | h) hx
    · exact h (forced x hx ▸ hx)
    · exact h (forced x hx)

end ProductPendingPatch
