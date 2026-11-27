import Std

namespace WitnessHeadVisits

/-- A finite piece of a native computation on a fixed immutable witness. -/
inductive Run (step : State → State → Prop) : State → State → Prop where
  | stay (s) : Run step s s
  | advance {s v w} : step s v → Run step v w → Run step s w

theorem Run.join (before : Run step u v) (after : Run step v w) :
    Run step u w := by
  induction before with
  | stay => exact after
  | advance h _ ih => exact .advance h (ih after)

/-- Port identifiers can be chosen while sweeping in arbitrary spatial
order. Agreement of exit and entry records gives a port at the same
configuration, with strictly less time remaining. -/
theorem acceptFromVisits {Port State : Type} (step : State → State → Prop)
    (entry : Port → State) (remaining : Port → Nat) (accept : State → Prop)
    (verified : ∀ p, (∃ z, Run step (entry p) z ∧ accept z) ∨
      ∃ q, remaining q < remaining p ∧ Run step (entry p) (entry q))
    (start : Port) : ∃ z, Run step (entry start) z ∧ accept z := by
  have all : ∀ d p, remaining p = d → ∃ z, Run step (entry p) z ∧ accept z := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro p eq
      rcases verified p with done | ⟨q, lt, first⟩
      · exact done
      · obtain ⟨z, last, final⟩ := ih (remaining q) (by omega) q rfl
        exact ⟨z, first.join last, final⟩
  exact all (remaining start) start rfl

/-- The positive bounded diagonal. A detected cheap proof is sound, while
the deterministic source signals on precisely the opposite answer. -/
theorem positiveReflection (sat cheap : Prop) (source : sat ↔ ¬ cheap)
    (checker : cheap → sat) : sat ∧ ¬ cheap := by
  have noCheap : ¬ cheap := fun h => (source.mp (checker h)) h
  exact ⟨source.mpr noCheap, noCheap⟩

def cost (weight : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | len+1 => cost weight start len + weight (start+len)

/-- Each cut in a consecutive hard band contributes its own crossings. -/
theorem hardBandCost (weight : Nat → Nat) (start n floor : Nat)
    (heavy : ∀ i, i < n → floor ≤ weight (start+i)) :
    n*floor ≤ cost weight start n := by
  induction n with
  | zero => simp [cost]
  | succ n ih =>
    have prefixBudget := ih (fun i hi => heavy i (by omega))
    have lastBudget := heavy n (by omega)
    simp only [cost, Nat.succ_mul]
    omega

/-- If the next usable cut is more than one block away, all b
successive cut positions in between are expensive. -/
theorem solidBandFromGap (usable : Nat → Prop) (lo hi b : Nat)
    (gap : lo+b < hi)
    (adjacent : ∀ j, lo < j → j < hi → ¬ usable j) :
    ∀ i, i < b → ¬ usable (lo+1+i) := by
  intro i bound
  exact adjacent _ (by omega) (by omega)


/-- One forward check accepts exactly the left subsequence. The other
    head compares the right subsequence backwards on the physical tape.
    Together they guarantee a permutation even with arbitrary output tags. -/
theorem mergeFromTwoScans {Record : Type} (output : List (Bool × Record))
    (left right : List Record)
    (forward : (output.filter Prod.fst).map Prod.snd = left)
    (backward : ((output.filter (fun p => !p.1)).map Prod.snd).reverse =
      right.reverse) :
    (left ++ right).Perm (output.map Prod.snd) := by
  have second := congrArg List.reverse backward
  simp only [List.reverse_reverse] at second
  rw [← forward, ← second, ← List.map_append]
  exact (List.filter_append_perm Prod.fst output).map _

def chain (last : Nat) (u v : Nat → Bool) : Prop :=
  u 0 = true ∧ v last = false ∧ ∀ i, i < last → v i = true → u (i+1) = true

/-- A locally satisfying pair with any specified nonzero discrepancy.
The first set coordinate in the discrepancy is j. -/
theorem everyDiscrepancy (last j : Nat) (delta : Nat → Bool) (range : j ≤ last)
    (first : delta j = true) (prior : ∀ i, i < j → delta i = false) :
    ∃ u v, chain last u v ∧ ∀ i, (u i != v i) = delta i := by
  let u := fun i => if i < j then true else delta i
  let v := fun i => decide (i < j)
  refine ⟨u, v, ⟨?_, ?_, ?_⟩, ?_⟩
  · by_cases h : 0 < j
    · simp [u, h]
    · have z : j = 0 := by omega
      simpa [u, z] using first
  · simp [v, Nat.not_lt.mpr range]
  · intro i _ hi
    have lt : i < j := by simpa [v] using hi
    by_cases eq : i+1 = j
    · simpa [u, eq] using first
    · have smaller : i+1 < j := by omega
      simp [u, smaller]
  · intro i
    by_cases h : i < j
    · simp [u, v, h, prior i h]
    · cases d : delta i <;> simp [u, v, h, d]

/-- Every strictly longer prefix of ones can pair with a shorter prefix.
Thus every two prefix strings must get distinct colors. -/
theorem prefixClique (last k j : Nat) (ordered : k < j) (bound : j ≤ last+1) :
    chain last (fun i => decide (i < j)) (fun i => decide (i < k)) := by
  constructor
  · simp only [decide_eq_true_eq]
    omega
  constructor
  · simp only [decide_eq_false_iff_not]
    omega
  · intro i _ hi
    simp only [decide_eq_true_eq] at hi ⊢
    omega

end WitnessHeadVisits
