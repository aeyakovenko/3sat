import Std

namespace NativeCoreExtensions

/-- Fixing the unique old assignment commutes with any existential extension. -/
theorem project_unique {Old Fresh : Type} (core : Old → Prop)
    (tau : Old) (unique : ∀ x, core x ↔ x = tau)
    (extra : Old → Fresh → Prop) :
    (∃ x y, core x ∧ extra x y) ↔ ∃ y, extra tau y := by
  constructor
  · rintro ⟨x, y, h, e⟩
    obtain rfl := (unique x).mp h
    exact ⟨y, e⟩
  · rintro ⟨y, e⟩
    exact ⟨tau, y, (unique tau).mpr rfl, e⟩

/-- Each bank clause has the semantics of z ∨ ¬u_i. -/
def bank {I : Type} (z : Bool) (u : I → Bool) : Prop :=
  ∀ i, z = true ∨ u i = false

theorem intact_bank {I : Type} (G : (I → Bool) → Prop) :
    (∃ z u, z = false ∧ bank z u ∧ G u) ↔ G (fun _ => false) := by
  constructor
  · rintro ⟨z, u, rfl, ok, h⟩
    have eqn : u = (fun _ => false) := by
      funext i
      simpa using ok i
    simpa [eqn] using h
  · intro h
    exact ⟨false, _, rfl, fun _ => Or.inr rfl, h⟩

theorem flipped_bank {I : Type} (G : (I → Bool) → Prop) :
    (∃ z u, z = true ∧ bank z u ∧ G u) ↔ ∃ u, G u := by
  constructor
  · rintro ⟨_, u, _, _, h⟩
    exact ⟨u, h⟩
  · rintro ⟨u, h⟩
    exact ⟨true, u, rfl, fun _ => Or.inl rfl, h⟩

theorem deleted_pin {I : Type} (G : (I → Bool) → Prop) :
    (∃ z u, bank z u ∧ G u) ↔ ∃ u, G u := by
  constructor
  · rintro ⟨_, u, _, h⟩
    exact ⟨u, h⟩
  · rintro ⟨u, h⟩
    exact ⟨true, u, fun _ => Or.inl rfl, h⟩

end NativeCoreExtensions
