import Std

namespace TwoBitPermutationSwitch

/-- Forward arrays P₀=[2,0,4,5,3,1], Q=[1,5,3,0,2,4].
At switch one, exchange the P images of columns 1 and 2.
The Q incidences of 5 and 4 receive external Boolean values x and y. -/
def rows (s x y h₀ h₁ h₂ h₃ h₄ h₅ : Bool) : List Nat :=
  let total := fun (a b c : Bool) => a.toNat + b.toNat + c.toNat
  [total h₀ (if s then h₂ else h₁) h₃, total h₁ h₅ h₀, total h₂ h₀ y,
   total h₃ h₄ h₂, total h₄ (if s then h₁ else h₂) x, total h₅ h₃ h₁]

abbrev allowed (s x y : Bool) : Prop :=
  (x = false ∧ y = false) ∨ (x = s ∧ y = !s)

set_option synthInstance.maxSize 512 in
/-- Full truth table, including the individual return values and all internal columns. -/
theorem open_rows : ∀ (s x y h₀ h₁ h₂ h₃ h₄ h₅ : Bool),
    rows s x y h₀ h₁ h₂ h₃ h₄ h₅ = [1,1,1,1,1,1] ↔
      h₅ = x ∧ h₄ = y ∧ allowed s x y ∧
      h₀ = false ∧ h₁ = !x ∧ h₂ = !y ∧ h₃ = false := by decide

abbrev boundary (s x y u v : Bool) : Prop :=
  ∃ h₀ h₁ h₂ h₃ : Bool, rows s x y h₀ h₁ h₂ h₃ v u = [1,1,1,1,1,1]

theorem boundary_iff : ∀ (s x y u v : Bool),
    boundary s x y u v ↔ u = x ∧ v = y ∧ allowed s x y := by decide

/-- Two fixed exchanges with arbitrary outside rows enforce the selected boundary pair. -/
theorem exchange {α : Type} (base : α → Bool → Bool → Prop) (a b : α → Bool) (s : Bool) :
    (∃ i u v, base i u v ∧ boundary s (a i) (b i) u v) ↔
    ∃ i, base i (a i) (b i) ∧ allowed s (a i) (b i) := by
  constructor
  · rintro ⟨i, u, v, outside, inside⟩
    obtain ⟨rfl, rfl, ok⟩ := (boundary_iff _ _ _ _ _).mp inside
    exact ⟨i, outside, ok⟩
  · rintro ⟨i, outside, ok⟩
    exact ⟨i, a i, b i, outside, (boundary_iff _ _ _ _ _).mpr ⟨rfl, rfl, ok⟩⟩

end TwoBitPermutationSwitch
