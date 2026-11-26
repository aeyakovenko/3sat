import Std

namespace PairedSatVerdictClaims

inductive Claim (ι : Type) where
  | negativeFile
  | negativeRun (i : ι)
  | positiveFile
  | positiveRun (i : ι)
  | disjunction

def Meaning {ι : Type} (g p : Prop) (no yes : ι → Prop) : Claim ι → Prop
  | .negativeFile => ¬ g
  | .negativeRun i => no i
  | .positiveFile => p
  | .positiveRun i => yes i
  | .disjunction => (¬ g) ∨ (∃ i, no i) ∨ p ∨ (∃ i, yes i)

/-- The compiler hypotheses describe the two physical files. The proof uses only
bounded soundness, correctness on those files, and uniqueness of a deterministic run. -/
theorem no_short_claim {ι α : Type} (g : Prop) (P : α → Prop)
    (met no yes : ι → Prop) (short : Claim ι → Prop)
    (negativeFile : g ↔ ∃ tag, short tag)
    (positiveFile : (∃ x, P x) ↔ ∃ i, met i ∧ no i)
    (deterministic : ∀ x y, P x → P y → y = x)
    (correctNo : ∀ i, no i ↔ ¬ g) (correctYes : ∀ i, yes i ↔ ∃ x, P x)
    (sound : ∀ tag, short tag → Meaning g (∃ x, P x) no yes tag) :
    (¬ g) ∧ (∀ i, no i) ∧ (∀ tag, ¬ short tag) ∧
    ((∀ i, ¬ met i) ∨ (∃ x, P x ∧ ∀ y, P y → y = x)) := by
  have ng : ¬ g := by
    intro hg
    have nno : ∀ i, ¬ no i := fun i hi => (correctNo i).mp hi hg
    have np : ¬ ∃ x, P x := by
      intro hp
      obtain ⟨i, _, hi⟩ := positiveFile.mp hp
      exact nno i hi
    have nyes : ∀ i, ¬ yes i := fun i hi => np ((correctYes i).mp hi)
    obtain ⟨tag, sh⟩ := negativeFile.mp hg
    have h := sound tag sh
    cases tag with
    | negativeFile => exact h hg
    | negativeRun i => exact nno i h
    | positiveFile => exact np h
    | positiveRun i => exact nyes i h
    | disjunction =>
      rcases h with fals | ⟨i, hi⟩ | hp | ⟨i, hi⟩
      · exact fals hg
      · exact nno i hi
      · exact np hp
      · exact nyes i hi
  have hn : ∀ i, no i := fun i => (correctNo i).mpr ng
  refine ⟨ng, hn, fun tag sh => ng (negativeFile.mpr ⟨tag, sh⟩), ?_⟩
  by_cases someMet : ∃ i, met i
  · obtain ⟨i, hi⟩ := someMet
    obtain ⟨x, hx⟩ := positiveFile.mpr ⟨i, hi, hn i⟩
    exact Or.inr ⟨x, hx, fun y hy => deterministic x y hx hy⟩
  · exact Or.inl fun i hi => someMet ⟨i, hi⟩

end PairedSatVerdictClaims
