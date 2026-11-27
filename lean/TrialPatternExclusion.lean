import Std

namespace TrialPatternExclusion

/-- The default follows whenever a chosen test would be realized by the
    synchronized outcome, and every eligible test soundly excludes realization. -/
theorem synchronized_default {State Pattern : Type} (actual fallback : State)
    (choice : Option Pattern) (eligible : Pattern → Prop)
    (realizes : State → Pattern → Prop)
    (chosen : ∀ p, choice = some p → eligible p)
    (synchronize : ∀ p, choice = some p → realizes actual p)
    (sound : ∀ p, eligible p → ¬ realizes actual p)
    (otherwise : choice = none → actual = fallback) :
    choice = none ∧ actual = fallback := by
  have empty : choice = none := by
    cases h : choice with
    | none => rfl
    | some p => exact False.elim (sound p (chosen p h) (synchronize p h))
  exact ⟨empty, otherwise empty⟩

/-- For an ordered scan of candidate Boolean patterns, sound refutations
    exclude every selected branch. All entries of the scan therefore failed,
    and every coordinate of the actual vector takes its default value. -/
theorem finite_pattern_exclusion {ι : Type} (candidates : List (ι → Bool))
    (refuted : (ι → Bool) → Bool) (actual fallback : ι → Bool)
    (rule : actual = (candidates.find? refuted).getD fallback)
    (sound : ∀ p ∈ candidates, refuted p = true → actual ≠ p) :
    candidates.find? refuted = none ∧ actual = fallback ∧
      ∀ p ∈ candidates, refuted p = false := by
  obtain ⟨noneChosen, eq⟩ := synchronized_default actual fallback
    (candidates.find? refuted) (fun p => p ∈ candidates ∧ refuted p = true) Eq
    (fun _ h => ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩)
    (fun _ h => by simpa [h] using rule)
    (fun p h => sound p h.1 h.2)
    (fun h => by simpa [h] using rule)
  refine ⟨noneChosen, eq, ?_⟩
  intro p hp
  exact Bool.of_not_eq_true ((List.find?_eq_none.mp noneChosen) p hp)

/-- A finite adaptive inspection of independent Boolean coordinates. -/
inductive Tree (ι Out : Type) : Type where
  | done (out : Out)
  | ask (i : ι) (no yes : Tree ι Out)

def run {ι Out} (w : ι → Bool) : Tree ι Out → Out
  | .done out => out
  | .ask i no yes => if w i then run w yes else run w no

def trace {ι Out} (w : ι → Bool) : Tree ι Out → List ι
  | .done _ => []
  | .ask i no yes => i :: (if w i then trace w yes else trace w no)

/-- Agreement only on the adaptive path taken at w suffices. -/
theorem replay {ι Out} (w alt : ι → Bool) (tree : Tree ι Out)
    (agree : ∀ i ∈ trace w tree, alt i = w i) :
    run alt tree = run w tree := by
  induction tree with
  | done => rfl
  | ask i no yes ih jh =>
    have head := agree i (by simp [trace])
    cases h : w i with
    | false =>
      simp only [run, head, h, Bool.false_eq_true, ↓reduceIte]
      apply ih
      intro a ha
      apply agree
      simp [trace, h, ha]
    | true =>
      simp only [run, head, h, ↓reduceIte]
      apply jh
      intro a ha
      apply agree
      simp [trace, h, ha]

/-- On independent bits a sound refutation must have read a scoped bit
    disagreeing with the purported pattern, even with adaptive queries. -/
theorem exposed_disagreement {ι} (scope w : ι → Bool)
    (tree : Tree ι (Option (ι → Bool))) (p : ι → Bool)
    (sound : ∀ alt q, run alt tree = some q → ¬ (∀ i, scope i = true → alt i = q i))
    (selected : run w tree = some p) :
    ∃ i ∈ trace w tree, scope i = true ∧ w i ≠ p i := by
  classical
  apply Classical.byContradiction
  intro absent
  let alt := fun i => if scope i then p i else w i
  have same : ∀ i ∈ trace w tree, alt i = w i := by
    intro i hi
    cases h : scope i with
    | false => simp [alt, h]
    | true =>
      have eq : w i = p i := Classical.byContradiction (fun ne => absent ⟨i, hi, h, ne⟩)
      simp [alt, h, eq]
  exact sound alt p ((replay w alt tree same).trans selected) (fun i h => by simp [alt, h])

/-- At a fixed world, mark outputs claiming to refute a pattern whose
    scoped coordinates are consistent with the entire observed transcript. -/
def unexposed {ι} (scope w : ι → Bool) (tree : Tree ι (Option (ι → Bool))) : Bool :=
  match run w tree with
  | none => false
  | some p => (trace w tree).all (fun i => !scope i || (w i == p i))

theorem sound_unexposed_false {ι} (scope w : ι → Bool) (tree : Tree ι (Option (ι → Bool)))
    (sound : ∀ alt q, run alt tree = some q → ¬ (∀ i, scope i = true → alt i = q i)) :
    unexposed scope w tree = false := by
  unfold unexposed
  cases h : run w tree with
  | none => rfl
  | some p =>
    obtain ⟨i, hi, hs, hn⟩ := exposed_disagreement scope w tree p sound h
    apply Bool.of_not_eq_true
    intro all
    have v := List.all_eq_true.mp all i hi
    simp [hs, hn] at v

/-- Any finite random seed distribution with integer weights assigns zero
    mass to these unexposed refutations if every positive-weight seed is
    sound on every bit completion. -/
theorem zero_unexposed_mass {ι σ} (scope w : ι → Bool) (seeds : List σ)
    (weight : σ → Nat) (tree : σ → Tree ι (Option (ι → Bool)))
    (sound : ∀ s, 0 < weight s →
      ∀ alt q, run alt (tree s) = some q → ¬ (∀ i, scope i = true → alt i = q i)) :
    (seeds.map (fun s => if unexposed scope w (tree s) then weight s else 0)).sum = 0 := by
  induction seeds with
  | nil => rfl
  | cons s rest ih =>
    by_cases z : weight s = 0
    · simp [z, ih]
    · have h := sound_unexposed_false scope w (tree s) (sound s (by omega))
      simp [h, ih]

end TrialPatternExclusion
