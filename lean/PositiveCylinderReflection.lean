import Std

namespace PositiveCylinderReflection

/-- An exact, timely decision for a sound one-sided predicate is negative wherever
    the target bit is its Boolean complement. -/
theorem cylinder_at (target bounded : Bool)
    (sound : bounded = true → target = true)
    (diagonal : target = !bounded) :
    target = true ∧ bounded = false := by
  cases bounded <;> simp_all

/-- All procedures whose affordable successes can be simulated inherit the
    absence of bounded witnesses at each such input. -/
theorem all_simulated (target bounded : X → Bool) (domain : X → Prop)
    (sound : ∀ x, bounded x = true → target x = true)
    (diagonal : ∀ x, domain x → target x = !(bounded x))
    (affordable : I → X → Prop)
    (sim : ∀ i x, affordable i x → bounded x = true) :
    ∀ x, domain x → target x = true ∧ ∀ i, ¬ affordable i x := by
  intro x hx
  obtain ⟨ht, hb⟩ := cylinder_at _ _ (sound x) (diagonal x hx)
  refine ⟨ht, ?_⟩
  intro i hi
  have yes := sim i x hi
  simp [hb] at yes

/-- In this branch every proof within the estimated total verification cost
    would yield a timely success. -/
theorem proof_cost (bounded : Bool) (absent : bounded = false)
    (proves : P → Prop) (cost : P → Nat) (cap : Nat)
    (fits : ∀ p, proves p → cost p ≤ cap → bounded = true) :
    ∀ p, proves p → cap < cost p := by
  intro p hp
  apply Nat.lt_of_not_ge
  intro h
  have yes := fits p hp h
  simp [absent] at yes

/-- A witness promised by a sound tail proof would itself enable the same
    test on the diagonal opponent, even if that particular run times out. -/
theorem tail_trigger_absent
    (trigger : M → Prop) (eligible : M → X → Prop) (positive : X → Prop)
    (witness : ∀ m, trigger m → ∃ x, eligible m x ∧ positive x)
    (persist : ∀ m x, trigger m → eligible m x → ¬positive x) :
    ∀ m, ¬trigger m := by
  intro m hm
  obtain ⟨x, hmx, hx⟩ := witness m hm
  exact persist m x hm hmx hx

end PositiveCylinderReflection
