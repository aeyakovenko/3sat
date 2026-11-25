import Std

namespace OneNegativePermutationPatch

/-- Six cubic exact-cover rows. The third D-row sees the external port v in
place of h0; the removed internal incidence has weight h0. -/
def rows (v d z₀ z₁ h₀ h₁ h₂ : Int) : List Int :=
  [d+h₁+h₂, d+h₂+h₀, d+v+h₁, z₀+z₁+h₀, z₀+z₁+h₁, z₀+z₁+h₂]

theorem local_conservation (v d z₀ z₁ h₀ h₁ h₂ : Int) :
    (rows v d z₀ z₁ h₀ h₁ h₂).sum + h₀ = 3*(d+z₀+z₁+h₀+h₁+h₂) + v := by
  simp [rows]
  omega

theorem binary_ports_match {v h₀ : Bool} {mass : Int}
    (conservation : 6 + (h₀.toNat : Int) = 3*mass + (v.toNat : Int)) : v = h₀ := by
  cases v <;> cases h₀ <;> simp_all <;> omega

abbrev feasible (v d z₀ z₁ h₀ h₁ h₂ : Bool) : Prop :=
  rows v.toNat d.toNat z₀.toNat z₁.toNat h₀.toNat h₁.toNat h₂.toNat = [1,1,1,1,1,1]

theorem Boolean_patch : ∀ (v d z₀ z₁ h₀ h₁ h₂ : Bool),
    feasible v d z₀ z₁ h₀ h₁ h₂ ↔
    v=false ∧ d=true ∧ z₀=!z₁ ∧ h₀=false ∧ h₁=false ∧ h₂=false := by decide

/-- Swapping the port of an arbitrary outside predicate pins its selected
bit. Here `base s b` evaluates the outside rows with b at the swapped edge. -/
theorem exchange_pins_false {α : Type} (base : α → Bool → Prop) (v : α → Bool) :
    (∃ s d z₀ z₁ h₀ h₁ h₂, base s h₀ ∧ feasible (v s) d z₀ z₁ h₀ h₁ h₂) ↔
    ∃ s, base s (v s) ∧ v s = false := by
  constructor
  · rintro ⟨s, d, z₀, z₁, h₀, h₁, h₂, outside, inside⟩
    obtain ⟨hv, _, _, hh, _, _⟩ := (Boolean_patch _ _ _ _ _ _ _).mp inside
    refine ⟨s, ?_, hv⟩
    rw [hv, ← hh]
    exact outside
  · rintro ⟨s, outside, hv⟩
    refine ⟨s, true, true, false, false, false, false, hv ▸ outside, ?_⟩
    rw [hv]
    decide

/-- One negative patch variable works when the external port is one. -/
theorem signed_patch : rows 1 (-1) 0 0 1 1 1 = [1,1,1,1,1,1] := by decide

theorem clipped_overlap : rows 1 0 0 0 1 1 1 = [2,2,2,1,1,1] := by decide

end OneNegativePermutationPatch
