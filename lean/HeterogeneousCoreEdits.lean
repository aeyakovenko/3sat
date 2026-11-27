import Std

namespace HeterogeneousCoreEdits

/-- Opposite highest-byte edits preserve the product for two different
    centers sharing their low byte. The word modulus is 256 * delta. -/
theorem mixed_product (a h scale e : Int) :
    256 * (256 * scale) ∣
      (a + e * (256 * scale)) * ((a + 256*h) - e * (256 * scale)) -
      a * (a + 256*h) := by
  refine ⟨e*h-e*e*scale, ?_⟩
  simp only [Int.mul_sub, Int.sub_mul, Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

def group (pin a b d : Bool) : Bool :=
  (pin || a || b) && (d || a || !b) && (d || !a || b) && (d || !a || !b)

theorem group_equivalent (pin a b d : Bool) :
    group pin a b d = ((pin || a || b) && (d || (!a && !b))) := by
  cases pin <;> cases a <;> cases b <;> cases d <;> decide

def pins (pin : Bool) (a b d : Fin 3 → Bool) : Prop :=
  (∀ j, group pin (a j) (b j) (d j) = true) ∧
  (d 0 = false ∨ d 1 = false ∨ d 2 = false)

theorem port_is_pinned (pin : Bool) : (∃ a b d, pins pin a b d) ↔ pin = true := by
  constructor
  · rintro ⟨a, b, d, groups, h⟩
    have local_pin : ∀ j, d j = false → pin = true := by
      intro j hj
      have step := groups j
      rw [group_equivalent, hj] at step
      cases pin <;> cases ha : a j <;> cases hb : b j <;> simp_all
    rcases h with h0 | h1 | h2
    · exact local_pin 0 h0
    · exact local_pin 1 h1
    · exact local_pin 2 h2
  · rintro rfl
    exact ⟨fun _ => false, fun _ => false, fun _ => false,
      fun _ => rfl, Or.inl rfl⟩

end HeterogeneousCoreEdits
