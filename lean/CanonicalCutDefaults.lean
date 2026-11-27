import Std

namespace CanonicalCutDefaults

/-- Each default is right on all cheap rows and on one color among the other rows. -/
theorem one_default_has_advantage (cheap outsideZero outsideOne : Nat) :
    cheap + cheap + outsideZero + outsideOne ≤ 2 * (cheap + outsideZero) ∨
    cheap + cheap + outsideZero + outsideOne ≤ 2 * (cheap + outsideOne) := by
  omega

/-- One affirmative marker among all candidate old prefixes is enough to decide
    any table. A negative input has no affirmative candidate carrying the marker. -/
theorem one_address_marker {α : Type} (wanted : α) (yes : α → Prop) :
    (∃ candidate, yes candidate ∧ candidate = wanted) ↔ yes wanted := by
  constructor
  · rintro ⟨candidate, h, rfl⟩
    exact h
  · intro h
    exact ⟨wanted, h, rfl⟩

theorem negative_queries_miss {α : Type} (wanted : α) (yes : α → Prop)
    (reject : ¬ yes wanted) (candidate : α) (query : yes candidate) :
    candidate ≠ wanted := by
  intro h
  exact reject (h ▸ query)

end CanonicalCutDefaults
