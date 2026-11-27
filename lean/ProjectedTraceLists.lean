import Std

/-! Finite parts of a nondeterministic verifier for projections of RAM logs.
The sink sees a list of positive timestamps of stores at one address before a
chosen read, in an arbitrary order. The word at each timestamp is part of the
projected log. Auxiliary labels have no effect on the projected tests. -/

namespace ProjectedTraceLists

/-- Zero represents the initial word. -/
def newest : List Nat → Nat
  | [] => 0
  | t :: ts => max t (newest ts)

theorem newestPerm {xs ys : List Nat} (perm : xs.Perm ys) :
    newest xs = newest ys := by
  induction perm with
  | nil => rfl
  | cons _ _ ih => simp [newest, ih]
  | swap => simp only [newest]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem newestAppend (xs ys : List Nat) :
    newest (xs ++ ys) = max (newest xs) (newest ys) := by
  induction xs with
  | nil => simp [newest]
  | cons t ts ih => simp only [List.cons_append, newest, ih]; omega

/-- Combining two disjoint parts of the stream preserves the largest stamp,
and looking up its word is independent of the arrival order. -/
theorem sameReadAfterPermutation (value : Nat → W) {xs ys : List Nat}
    (perm : xs.Perm ys) : value (newest xs) = value (newest ys) :=
  congrArg value (newestPerm perm)

/-- Existence and absence of a counterexample refer to the same filter.
They can be separate nondeterministic tests with opposite signs. -/
theorem soundSignals {Label Trace : Type} (accept : Label → Prop)
    (view : Label → Trace) (good : Trace → Prop)
    (nonempty : ∃ x, accept x)
    (noBad : ¬∃ x, accept x ∧ ¬good (view x)) :
    ∃ x, accept x ∧ good (view x) := by
  classical
  obtain ⟨x, hx⟩ := nonempty
  exact ⟨x, hx, Classical.byContradiction (fun bad => noBad ⟨x, hx, bad⟩)⟩

/-- A remainder or another statistic can isolate a *projection* even when
many different labels realize the chosen projection. -/
theorem isolateProjection {Label Trace Key : Type} (accept : Label → Prop)
    (view : Label → Trace) (key : Trace → Key) (real : Trace)
    (represents : ∃ x, accept x ∧ view x = real)
    (separates : ∀ x, accept x → view x ≠ real → key (view x) ≠ key real) :
    (∃ x, accept x ∧ key (view x) = key real) ∧
    (∀ x, accept x → key (view x) = key real → view x = real) := by
  classical
  obtain ⟨x, hx, pv⟩ := represents
  exact ⟨⟨x, hx, congrArg key pv⟩,
    fun y hy same => Classical.byContradiction (fun bad => separates y hy bad same)⟩

/-- Every candidate prime blocked by some projected transcript is enumerated.
Duplicates among blocked keys only make this counting bound weaker. -/
theorem avoidBlockedKeys {K : Type} [DecidableEq K] (bans choices : List K)
    (distinct : choices.Nodup) (room : bans.length < choices.length) :
    ∃ k, k ∈ choices ∧ k ∉ bans := by
  induction bans generalizing choices with
  | nil =>
    cases choices with
    | nil => simp at room
    | cons k ks => exact ⟨k, by simp, by simp⟩
  | cons a tail ih =>
    have retain := List.le_length_erase (a := a) (l := choices)
    have spare : tail.length < (choices.erase a).length := by
      simp only [List.length_cons] at room
      omega
    obtain ⟨k, hk, good⟩ := ih (choices.erase a) (distinct.erase a) spare
    have diff : k ≠ a := by
      intro same
      subst k
      exact distinct.not_mem_erase hk
    exact ⟨k, List.mem_of_mem_erase hk, by simp [diff, good]⟩

theorem finiteSeparation {K T : Type} [DecidableEq K] (tries : List T)
    (choices : List K) (cover : T → List K) (perTrace : Nat)
    (bounded : ∀ t ∈ tries, (cover t).length ≤ perTrace)
    (uniqueChoices : choices.Nodup)
    (enough : tries.length * perTrace < choices.length) :
    ∃ k, k ∈ choices ∧ ∀ t ∈ tries, k ∉ cover t := by
  have total : (tries.flatMap cover).length ≤ tries.length * perTrace := by
    induction tries with
    | nil => simp
    | cons t ts ih =>
      have head := bounded t (by simp)
      have tail := ih (fun x hx => bounded x (by simp [hx]))
        (by simp only [List.length_cons, Nat.succ_mul] at enough; omega)
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      omega
  obtain ⟨k, hk, ok⟩ := avoidBlockedKeys (tries.flatMap cover) choices uniqueChoices
    (Nat.lt_of_le_of_lt total enough)
  exact ⟨k, hk, fun t ht blocked => ok (List.mem_flatMap_of_mem ht blocked)⟩

/-- A revealed true value at every possible first disagreeing coordinate
eliminates every other projected string. -/
theorem firstDifferencesTeach {Word : Type} (size : Nat)
    (real attempt : Nat → Word) (marked : Nat → Prop)
    (markFirst : ∀ j, j < size → (∀ i, i < j → attempt i = real i) →
      attempt j ≠ real j → marked j)
    (agrees : ∀ j, j < size → marked j → attempt j = real j) :
    ∀ j, j < size → attempt j = real j := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j prev =>
    intro hj
    exact Classical.byContradiction fun diff =>
      diff (agrees j hj (markFirst j hj (fun i hi => prev i hi (by omega)) diff))

/-- A bucket audit can certify that no good accepting projection exists.
The challenge can depend on the bucket and need not be computable from it. -/
theorem noTrueAcceptAcrossBuckets {T Key Challenge : Type}
    (candidate good : T → Prop) (tag : T → Key) (fault : Challenge → T → Prop)
    (noFaultOnGood : ∀ t, good t → ∀ j, ¬fault j t)
    (cover : ∀ k, ∃ j, ∀ t, candidate t → tag t = k → fault j t) :
    ¬∃ t, candidate t ∧ good t := by
  rintro ⟨t, possible, genuine⟩
  obtain ⟨j, blocks⟩ := cover (tag t)
  exact noFaultOnGood t genuine j (blocks t possible rfl)

/-- If a small fingerprint can distinguish all admitted projections, each
nonempty bucket has a common local challenge whenever each candidate has one. -/
theorem bucketCoverFromSeparation {T Key Challenge : Type} [Nonempty Challenge]
    (candidate : T → Prop) (tag : T → Key) (fault : Challenge → T → Prop)
    (unique : ∀ a b, candidate a → candidate b → tag a = tag b → a = b)
    (someFault : ∀ t, candidate t → ∃ j, fault j t) :
    ∀ k, ∃ j, ∀ t, candidate t → tag t = k → fault j t := by
  classical
  intro k
  by_cases occ : ∃ a, candidate a ∧ tag a = k
  · obtain ⟨a, ha, hk⟩ := occ
    obtain ⟨j, bad⟩ := someFault a ha
    refine ⟨j, ?_⟩
    intro t ht tk
    have same := unique t a ht ha (tk.trans hk.symm)
    simpa [same] using bad
  · exact ⟨Classical.choice (inferInstance : Nonempty Challenge),
      fun t ht tk => (occ ⟨t, ht, tk⟩).elim⟩

end ProjectedTraceLists
