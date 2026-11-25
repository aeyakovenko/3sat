import Std

namespace ComplementaryNameProjection

/-- A pair of positive names ends respectively in the ASCII digits zero and one.
The second member stores the source bit. A unit selects the first or second name. -/
def Pin (bit first second : Bool) : Prop :=
  (first || second) = true ∧
  (!first || !second) = true ∧
  (if bit then second else first) = true

theorem pin_iff (bit first second : Bool) :
    Pin bit first second ↔ first = !bit ∧ second = bit := by
  cases bit <;> cases first <;> cases second <;> simp [Pin]

/-- The public constraints can express any predicate on the second names. -/
def Models {I : Type} (condition : (I → Bool) → Prop) (data : I → Bool)
    (names : (I → Bool) × (I → Bool)) : Prop :=
  condition names.2 ∧ ∀ i, Pin (data i) (names.1 i) (names.2 i)

theorem models_iff {I : Type} (condition : (I → Bool) → Prop) (data : I → Bool)
    (names : (I → Bool) × (I → Bool)) :
    Models condition data names ↔
      condition data ∧ names = ((fun i => !(data i)), data) := by
  constructor
  · rintro ⟨holds, pins⟩
    have first : names.1 = fun i => !(data i) :=
      funext fun i => ((pin_iff ..).1 (pins i)).1
    have second : names.2 = data :=
      funext fun i => ((pin_iff ..).1 (pins i)).2
    exact ⟨second ▸ holds, Prod.ext first second⟩
  · rintro ⟨holds, rfl⟩
    exact ⟨holds, fun i => (pin_iff ..).2 ⟨rfl, rfl⟩⟩

end ComplementaryNameProjection
