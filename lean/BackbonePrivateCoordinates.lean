import Std

namespace BackbonePrivateCoordinates

/-- A model in a minimal cover has a literal value that the other models
cannot witness. In a cover of at least three models, their coordinates are
already distinct, even after forgetting the private values' signs. -/
theorem private_coordinates_injective {Model Coordinate : Type}
    (value : Model → Coordinate → Bool) (coord : Model → Coordinate)
    (privateValue : ∀ x y, x ≠ y → value y (coord x) ≠ value x (coord x))
    (third : ∀ x y : Model, x ≠ y → ∃ z : Model, z ≠ x ∧ z ≠ y)
    (x y : Model) (same : coord x = coord y) : x = y := by
  by_cases eq : x = y
  · exact eq
  · obtain ⟨z, zx, zy⟩ := third x y eq
    have hxy := privateValue x y eq
    have hxz := privateValue x z (Ne.symm zx)
    have hyz := privateValue y z (Ne.symm zy)
    rw [← same] at hyz
    cases h₁ : value x (coord x) <;>
      cases h₂ : value y (coord x) <;>
      cases h₃ : value z (coord x) <;>
      simp [h₁, h₂, h₃] at *

/-- If deleting a row loses some previously witnessed literal, that row
owned a private value on its coordinate. -/
theorem private_of_deletion {Model Coordinate : Type}
    (value : Model → Coordinate → Bool) (row : Model)
    (deletion : ∃ j b, (∃ w, value w j = b) ∧
                          ∀ w, w ≠ row → value w j ≠ b) :
    ∃ j, ∀ w, row ≠ w → value w j ≠ value row j := by
  obtain ⟨j, b, ⟨w, hw⟩, gone⟩ := deletion
  have owner : w = row := by
    by_cases eq : w = row
    · exact eq
    · exact (gone w eq hw).elim
  subst w
  exact ⟨j, fun w h => hw.symm ▸ gone w (Ne.symm h)⟩

end BackbonePrivateCoordinates
