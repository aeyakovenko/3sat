import Std

namespace SatNamePolarity

/-- Positions in a fixed formula acquire input-dependent variable names.
    The predicate holds of the literal values before signs and clauses
    are interpreted, so the argument works for any fixed formula. -/
def SatWith (ok : (I → Bool) → Prop) (names : I → V) : Prop :=
  ∃ assign : V → Bool, ok (assign ∘ names)

/-- Extend any consistent coloring of the occurrences to the named variables. -/
theorem extendColor (names : I → V) (bits : I → Bool)
    (consistent : ∀ i j, names i = names j → bits i = bits j) :
    ∃ assign : V → Bool, assign ∘ names = bits := by
  classical
  let assign := fun v => decide (∃ i, names i = v ∧ bits i = true)
  refine ⟨assign, funext fun i => ?_⟩
  change decide (∃ j, names j = names i ∧ bits j = true) = bits i
  cases h : bits i with
  | false =>
    apply decide_eq_false
    rintro ⟨j, eqname, yes⟩
    have eqbit := consistent j i eqname
    simp_all
  | true =>
    apply decide_eq_true
    exact ⟨i, rfl, h⟩

theorem pullback (ok : (I → Bool) → Prop) (old : I → V) (new : I → W)
    (merge : ∀ i j, old i = old j → new i = new j)
    (accept : SatWith ok new) : SatWith ok old := by
  obtain ⟨color, valid⟩ := accept
  obtain ⟨assign, eq⟩ := extendColor old (color ∘ new)
    (fun i j h => congrArg color (merge i j h))
  exact ⟨assign, eq.symm ▸ valid⟩

/-- On a false input, two incompatible colors in this particular witness
    for the true input must collide. -/
theorem oppositeCollision (ok : (I → Bool) → Prop) (names : I → V)
    (bits : I → Bool) (good : ok bits) (bad : ¬ SatWith ok names) :
    ∃ i j, names i = names j ∧ bits i ≠ bits j := by
  classical
  apply Classical.byContradiction
  intro no
  have consistent : ∀ i j, names i = names j → bits i = bits j := by
    intro i j same
    apply Classical.byContradiction
    exact fun diff => no ⟨i, j, same, diff⟩
  obtain ⟨assign, eq⟩ := extendColor names bits consistent
  exact bad ⟨assign, eq.symm ▸ good⟩

/-- When a previously unsatisfiable formula becomes satisfiable, some
    equality of its names must split, regardless of new collisions. -/
theorem splitCollision (ok : (I → Bool) → Prop) (old : I → V) (new : I → W)
    (bad : ¬ SatWith ok old) (good : SatWith ok new) :
    ∃ i j, old i = old j ∧ new i ≠ new j := by
  classical
  apply Classical.byContradiction
  intro no
  apply bad
  apply pullback ok old new _ good
  intro i j eq
  apply Classical.byContradiction
  exact fun diff => no ⟨i, j, eq, diff⟩

end SatNamePolarity
