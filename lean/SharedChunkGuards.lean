import Std

namespace SharedChunkGuards

/-- Every possible selection of one chunk per label meets a match exactly when
one label matches throughout. The chunk type may depend on the label. -/
theorem whole_match_iff_guards {Label : Type u} {Chunk : Label → Type v}
    (matchAt : (i : Label) → Chunk i → Prop) :
    (∃ i, ∀ c, matchAt i c) ↔
      (∀ choose : (i : Label) → Chunk i, ∃ i, matchAt i (choose i)) := by
  classical
  constructor
  · rintro ⟨i, whole⟩ choose
    exact ⟨i, whole (choose i)⟩
  · intro guards
    apply Classical.byContradiction
    intro noWhole
    have failed (i : Label) : ∃ c, ¬ matchAt i c := by
      apply Classical.not_forall.mp
      exact fun allMatch => noWhole ⟨i, allMatch⟩
    let choose (i : Label) := Classical.choose (failed i)
    obtain ⟨i, hit⟩ := guards choose
    exact Classical.choose_spec (failed i) hit

/-- The final high field is incorporated into the flag for the database mask.
Forbidding simultaneous matches on all three fields, using the corresponding
block's mask, accepts precisely when the selected bit is one. -/
theorem mask_clauses_iff_selected_bit {A B C Offset : Type}
    (data : A → B → C → Offset → Bool)
    (addressA : A) (addressB : B) (addressC : C) (offset : Offset) :
    (∀ a b c,
        ¬ (addressA = a ∧ addressB = b ∧
            (addressC = c ∧ data a b c offset = false))) ↔
      data addressA addressB addressC offset = true := by
  constructor
  · intro clauses
    have good := clauses addressA addressB addressC
    cases h : data addressA addressB addressC offset with
    | false => exact False.elim (good ⟨rfl, rfl, rfl, h⟩)
    | true => rfl
  · rintro good _ _ _ ⟨rfl, rfl, rfl, bad⟩
    exact Bool.noConfusion (good.symm.trans bad)

end SharedChunkGuards
