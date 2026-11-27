import Std

namespace PrivateTrialCores

variable {Cell : Type} {Private : Cell → Type} {Verdict : Type}

/-- Private assignments at different cells share only the exported Boolean. -/
def extendible (part : (u : Cell) → Bool → Private u → Prop) (x : Cell → Bool) : Prop :=
  ∃ a : (u : Cell) → Private u, ∀ u, part u (x u) (a u)

def forces (part : (u : Cell) → Bool → Private u → Prop) (truth : Cell → Bool)
    (u : Cell) : Prop := ¬ ∃ a, part u (!(truth u)) a

/-- The possible signal tables of any fragment form exactly the subcube given
    by its forced entries, provided the fragment admits the honest table. -/
theorem rectangle (part : (u : Cell) → Bool → Private u → Prop) (truth x : Cell → Bool)
    (honest : extendible part truth) :
    extendible part x ↔ ∀ u, forces part truth u → x u = truth u := by
  classical
  constructor
  · rintro ⟨a, h⟩ u hu
    apply Classical.byContradiction
    intro neq
    have flip : x u = !(truth u) := by cases hx : x u <;> cases ht : truth u <;> simp_all
    exact hu ⟨a u, flip ▸ h u⟩
  · intro fixed
    obtain ⟨good, hg⟩ := honest
    have each : ∀ u, ∃ a, part u (x u) a := by
      intro u
      by_cases eq : x u = truth u
      · exact ⟨good u, eq ▸ hg u⟩
      · have free : ¬ forces part truth u := fun h => eq (fixed u h)
        have other : ∃ a, part u (!(truth u)) a := Classical.byContradiction free
        have flip : x u = !(truth u) := by cases hx : x u <;> cases ht : truth u <;> simp_all
        exact flip ▸ other
    exact ⟨fun u => Classical.choose (each u), fun u => Classical.choose_spec (each u)⟩

/-- For the full outer scheduler, obstruction is exactly the certificate
    condition on the bits forced by the selected inner clauses. -/
theorem pin_impossible (part : (u : Cell) → Bool → Private u → Prop) (truth : Cell → Bool)
    (honest : extendible part truth) (winner : (Cell → Bool) → Verdict) (pin : Verdict) :
    (¬ ∃ x, extendible part x ∧ winner x = pin) ↔
      ∀ x, (∀ u, forces part truth u → x u = truth u) → winner x ≠ pin := by
  constructor
  · rintro h x fixed eq
    exact h ⟨x, (rectangle part truth x honest).mpr fixed, eq⟩
  · rintro h ⟨x, ok, eq⟩
    exact h x ((rectangle part truth x honest).mp ok) eq

/-- A change to a single decisive trial forces all refutations to pin it. -/
theorem decisive_cell (part : (u : Cell) → Bool → Private u → Prop) (truth alt : Cell → Bool)
    (honest : extendible part truth) (winner : (Cell → Bool) → Verdict) (pin : Verdict)
    (target : Cell) (agree : ∀ u, u ≠ target → alt u = truth u) (changed : winner alt = pin)
    (refuted : ¬ ∃ x, extendible part x ∧ winner x = pin) : forces part truth target := by
  classical
  apply Classical.byContradiction
  intro free
  apply (pin_impossible part truth honest winner pin).mp refuted alt _ changed
  intro u forced
  exact agree u (fun eq => free (eq ▸ forced))

end PrivateTrialCores
