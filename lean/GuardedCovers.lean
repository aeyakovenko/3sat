import Std

namespace GuardedCovers

/-- A union of cubes is the conjunction of all clauses obtained by picking
one literal from each cube. With w cubes each selected clause has width ≤ w. -/
theorem distribute_cubes {ι : Type} {Lit : ι → Type} (holds : (i : ι) → Lit i → Prop) :
    (∃ i, ∀ j, holds i j) ↔
    (∀ pick : (i : ι) → Lit i, ∃ i, holds i (pick i)) := by
  constructor
  · rintro ⟨i, good⟩ pick
    exact ⟨i, good (pick i)⟩
  · classical
    intro allPicks
    by_cases good : ∃ i, ∀ j, holds i j
    · exact good
    · have missing (i : ι) : ∃ j, ¬ holds i j := by
        apply Classical.byContradiction
        intro noMissing
        apply good
        exact ⟨i, fun j => Classical.byContradiction (fun h => noMissing ⟨j, h⟩)⟩
      obtain ⟨i, ok⟩ := allPicks (fun i => Classical.choose (missing i))
      exact False.elim ((Classical.choose_spec (missing i)) ok)

/-- A projection may, for instance, read a fixed set of w coordinates. -/
def Admitted (proj : ι → β → γ) (inserted : List β) (v : β) : Prop :=
  ∀ i, ∃ old, old ∈ inserted ∧ proj i v = proj i old

/-- One conjunction of forbidden projection patterns. -/
def Fits (proj : ι → β → γ) (allowed : ι → γ → Prop) (v : β) : Prop :=
  ∀ i, allowed i (proj i v)

theorem inherits (proj : ι → β → γ) (allowed : ι → γ → Prop)
    {inserted : List β} {v : β} (fits : ∀ old ∈ inserted, Fits proj allowed old)
    (admit : Admitted proj inserted v) : Fits proj allowed v := by
  intro i
  obtain ⟨old, mem, eq⟩ := admit i
  rw [eq]
  exact fits old mem i

/-- Start with the actual initial observations. An admitted source can
provide an inserted successor even when the source did not occur earlier. -/
inductive Record (proj : ι → β → γ) (obs : σ → β) (edge : σ → σ → Prop)
    (start : σ) : List β → Prop where
  | initial : Record proj obs edge start [obs start]
  | insert {seen : List β} {a b : σ} : Record proj obs edge start seen →
      Admitted proj seen (obs a) → edge a b → Record proj obs edge start (obs b :: seen)

theorem Record.respects {proj : ι → β → γ} {obs : σ → β} {edge : σ → σ → Prop}
    {start : σ} {seen : List β} (steps : Record proj obs edge start seen)
    (allowed : ι → γ → Prop) (initial : Fits proj allowed (obs start))
    (advance : ∀ a b, Fits proj allowed (obs a) → edge a b → Fits proj allowed (obs b)) :
    ∀ v ∈ seen, Fits proj allowed v := by
  induction steps with
  | initial =>
    intro v mem
    have h : v = obs start := List.mem_singleton.mp mem
    exact h.symm ▸ initial
  | @insert seen a b _ admit step ih =>
    intro v mem
    rcases List.mem_cons.mp mem with eq | old
    · subst v
      exact advance a b (inherits proj allowed ih admit) step
    · exact ih v old

theorem failure_excludes_safe_conjunction {proj : ι → β → γ} {obs : σ → β}
    {edge : σ → σ → Prop} {start : σ} {seen : List β} (steps : Record proj obs edge start seen)
    (bad : σ → Prop) {stop : σ} (request : Admitted proj seen (obs stop)) (isBad : bad stop) :
    ¬ ∃ allowed : ι → γ → Prop, Fits proj allowed (obs start) ∧
      (∀ a b, Fits proj allowed (obs a) → edge a b → Fits proj allowed (obs b)) ∧
      (∀ s, Fits proj allowed (obs s) → ¬ bad s) := by
  rintro ⟨allowed, initial, advance, excludes⟩
  exact excludes stop (inherits proj allowed (steps.respects allowed initial advance) request) isBad

/-- At saturation the allowed patterns are exactly those already seen on
each projection. This gives an actual safe inductive conjunction. -/
theorem saturated_gives_conjunction (proj : ι → β → γ) (obs : σ → β) (edge : σ → σ → Prop)
    (bad : σ → Prop) (start : σ) (seen : List β) (initial : obs start ∈ seen)
    (closed : ∀ a b, Admitted proj seen (obs a) → edge a b → Admitted proj seen (obs b))
    (excludes : ∀ s, Admitted proj seen (obs s) → ¬ bad s) :
    ∃ allowed : ι → γ → Prop, Fits proj allowed (obs start) ∧
      (∀ a b, Fits proj allowed (obs a) → edge a b → Fits proj allowed (obs b)) ∧
      (∀ s, Fits proj allowed (obs s) → ¬ bad s) := by
  refine ⟨fun i val => ∃ v, v ∈ seen ∧ val = proj i v, ?_, closed, excludes⟩
  intro i
  exact ⟨obs start, initial, rfl⟩

end GuardedCovers
