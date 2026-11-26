import Std

namespace PrefixMenuLoss

/-- The default drops the whole zero block of a finite menu.
    The predicate p may designate a full source witness, and label is its prefix. -/
theorem loss_projects {A I T : Type} (p : A → Prop) (label : A → I)
    (zero : I → Prop) (tag : T → I → Bool)
    (active : ∃ a, p a)
    (defaultLost : ¬ ∃ a, p a ∧ ¬ zero (label a))
    (fixedZero : ∀ z i, zero i → tag z i = false) :
    (∀ a, p a → zero (label a)) ∧
    (∀ z side a, (p a ∧ tag z (label a) = side) ↔ (p a ∧ side = false)) ∧
    (∀ z side, (∃ a, p a ∧ tag z (label a) = side) ↔ side = false) := by
  classical
  have inside (a : A) (ha : p a) : zero (label a) := by
    apply Classical.byContradiction
    intro hn
    exact defaultLost ⟨a, ha, hn⟩
  have fibers (z : T) (side : Bool) (a : A) :
      (p a ∧ tag z (label a) = side) ↔ (p a ∧ side = false) := by
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨ha, h.symm.trans (fixedZero z _ (inside a ha))⟩
    · rintro ⟨ha, rfl⟩
      exact ⟨ha, fixedZero z _ (inside a ha)⟩
  refine ⟨inside, fibers, ?_⟩
  intro z side
  constructor
  · rintro ⟨a, h⟩
    exact ((fibers z side a).mp h).2
  · obtain ⟨a, ha⟩ := active
    exact fun h => ⟨a, (fibers z side a).mpr ⟨ha, h⟩⟩

/-- A timely YES keeps the indicated subset. A timely NO keeps its complement. -/
theorem replied_cut_keeps_model {A : Type} (p cut : A → Prop) (answer : Bool)
    (sound : (answer = true) ↔ ∃ a, p a ∧ cut a) (active : ∃ a, p a) :
    ∃ a, p a ∧ (cut a ↔ answer = true) := by
  classical
  by_cases pos : answer = true
  · obtain ⟨a, ha, hcut⟩ := sound.mp pos
    exact ⟨a, ha, ⟨fun _ => pos, fun _ => hcut⟩⟩
  · obtain ⟨a, ha⟩ := active
    exact ⟨a, ha, ⟨fun h => False.elim (pos (sound.mpr ⟨a, ha, h⟩)),
                   fun h => False.elim (pos h)⟩⟩

end PrefixMenuLoss
