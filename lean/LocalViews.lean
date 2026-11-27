import Std

namespace LocalViews

/-- A view lists the proof bits used when the verifier runs on one challenge. -/
structure Read (Address : Type) where
  addr : Address
  val : Bool

def agrees (p : A → Bool) (view : List (Read A)) : Prop :=
  ∀ b ∈ view, p b.addr = b.val

/-- Glue any compatible subfamily. This also handles repeated reads within one
view. Choosing a default on unused addresses is allowed. -/
theorem glue (keep : R → Prop) (views : R → List (Read A))
    (compatible : ∀ r, keep r → ∀ s, keep s →
      ∀ a ∈ views r, ∀ b ∈ views s, a.addr = b.addr → a.val = b.val) :
    ∃ p, ∀ r, keep r → agrees p (views r) := by
  classical
  let witness (i : A) : Prop :=
    ∃ s, keep s ∧ ∃ b ∈ views s, b.addr = i ∧ b.val = true
  refine ⟨fun i => decide (witness i), ?_⟩
  intro r hr a ha
  cases h : a.val with
  | true =>
    have hw : witness a.addr := ⟨r, hr, a, ha, rfl, h⟩
    simpa using (decide_eq_true hw)
  | false =>
    have hw : ¬ witness a.addr := by
      rintro ⟨s, hs, b, hb, hab, hv⟩
      have he := compatible r hr s hs a ha b hb hab.symm
      simp [h, hv] at he
    simpa using (decide_eq_false hw)

/-- A monotone Boolean aggregation of universally valid tests can be checked
against a tuple of independent adversarial challenges in one universal block. -/
theorem universal_aggregate {I W : Type} [Nonempty W]
    (agg : (I → Prop) → Prop)
    (mono : ∀ P Q, (∀ i, P i → Q i) → agg P → agg Q)
    (test : I → W → Prop) :
    agg (fun i => ∀ w, test i w) ↔ ∀ ws : I → W, agg (fun i => test i (ws i)) := by
  classical
  constructor
  · intro h ws
    exact mono _ _ (fun i hi => hi (ws i)) h
  · intro h
    let worst (i : I) : W := if bad : ∃ w, ¬ test i w
      then Classical.choose bad else Classical.choice inferInstance
    apply mono _ _ _ (h worst)
    intro i hi w
    apply Classical.byContradiction
    intro hbad
    have bad : ∃ u, ¬ test i u := ⟨w, hbad⟩
    have contra : ¬ test i (worst i) := by
      simpa [worst, bad] using (Classical.choose_spec bad)
    exact contra hi

#print axioms glue
#print axioms universal_aggregate

end LocalViews
