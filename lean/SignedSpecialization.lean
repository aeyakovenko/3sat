import Std

namespace SignedSpecialization

/-- The signed source, chart soundness, and the two branches of one targeted
wrapper at a fixed vertex. On the fallback branch its reference is correct. -/
structure Vertex (desired truth output chart shortcut : Bool) : Prop where
  signed : truth = (desired ^^ chart)
  chartSound : chart = true → output = desired
  fallback : shortcut = false → output = truth
  cheapChart : shortcut = true → chart = true

theorem programmable_truth {desired truth output chart shortcut : Bool}
    (v : Vertex desired truth output chart shortcut) :
    chart = shortcut ∧ truth = (desired ^^ shortcut) ∧ output = desired := by
  obtain ⟨hs, hc, hf, hq⟩ := v
  cases shortcut <;> cases chart <;> cases desired <;> simp_all

theorem shortcut_valid_iff {desired truth output chart shortcut : Bool}
    (v : Vertex desired truth output chart shortcut) :
    truth = desired ↔ shortcut = false := by
  obtain ⟨_, ht, _⟩ := programmable_truth v
  cases desired <;> cases shortcut <;> simp_all

/-- The shortcut flag is common to a length. Every length has at least one
sign vector, including length zero. -/
theorem whole_cube {k : Nat} {desired truth output chart : (Fin k → Bool) → Bool}
    {shortcut : Bool}
    (v : ∀ b, Vertex (desired b) (truth b) (output b) (chart b) shortcut) :
    (∀ b, truth b = desired b) ↔ shortcut = false := by
  constructor
  · intro h
    exact (shortcut_valid_iff (v (fun _ => false))).mp (h _)
  · intro h b
    exact (shortcut_valid_iff (v b)).mpr h

/-- A stage schedule tending to infinity and representing every large stage
at a late length transfers eventual correctness in both directions. -/
theorem eventual_validity
    (good : Nat → Prop) (event : Nat → Bool) (stage : Nat → Nat) (cutoff : Nat)
    (pointwise : ∀ k, cutoff ≤ k → (good k ↔ event (stage k) = false))
    (lateStages : ∀ s, ∃ K, ∀ k, K ≤ k → s ≤ stage k)
    (represented : ∀ s, ∃ k, s ≤ k ∧ stage k = s) :
    (∃ K, ∀ k, K ≤ k → good k) ↔ (∃ S, ∀ s, S ≤ s → event s = false) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨max cutoff K, ?_⟩
    intro s hs
    obtain ⟨k, hsk, hstage⟩ := represented s
    have hc : cutoff ≤ k := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans hs hsk)
    have hk : K ≤ k := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans hs hsk)
    simpa only [hstage] using (pointwise k hc).mp (hK k hk)
  · rintro ⟨S, hS⟩
    obtain ⟨K, hK⟩ := lateStages S
    refine ⟨max cutoff K, ?_⟩
    intro k hk
    exact (pointwise k (Nat.le_trans (Nat.le_max_left _ _) hk)).mpr
      (hS _ (hK k (Nat.le_trans (Nat.le_max_right _ _) hk)))

end SignedSpecialization
