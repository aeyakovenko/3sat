import Std

namespace GluedBoundaryTables

abbrev Rel (ι : Type) := ι → Prop

def separated (s t : Rel ι) : Prop := ∀ i, ¬ (s i ∧ t i)

def complement (s : Rel ι) : Rel ι := fun i => ¬ s i

def join (s₀ s₁ : Rel ι) : Rel (Bool × ι) :=
  fun p => if p.1 then s₁ p.2 else s₀ p.2

theorem join_separated (s₀ s₁ t₀ t₁ : Rel ι) :
    separated (join s₀ s₁) (join t₀ t₁) ↔
      separated s₀ t₀ ∧ separated s₁ t₁ := by
  constructor
  · intro h
    exact ⟨fun i => h (false, i), fun i => h (true, i)⟩
  · rintro ⟨h₀, h₁⟩ ⟨b, i⟩
    cases b
    · exact h₀ i
    · exact h₁ i

theorem self_complement (s : Rel ι) : separated s (complement s) :=
  fun _ h => h.2 h.1

theorem crossed_separation (s t : Rel ι)
    (h : separated s (complement t)) (g : separated t (complement s)) : s = t := by
  classical
  funext i
  apply propext
  constructor
  · intro hs
    exact Classical.byContradiction (fun ht => h i ⟨hs, ht⟩)
  · intro ht
    exact Classical.byContradiction (fun hs => g i ⟨ht, hs⟩)

theorem exact_summary_injective (summary : Rel ι → σ)
    (decode : σ → Rel ι → Prop)
    (exactDecode : ∀ s t, decode (summary s) t ↔ separated s t)
    {s t : Rel ι} (equal : summary s = summary t) : s = t := by
  apply crossed_separation
  · apply (exactDecode s (complement t)).mp
    rw [equal]
    exact (exactDecode t (complement t)).mpr (self_complement t)
  · apply (exactDecode t (complement s)).mp
    rw [← equal]
    exact (exactDecode s (complement s)).mpr (self_complement s)

end GluedBoundaryTables
