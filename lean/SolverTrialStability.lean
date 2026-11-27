import Std

namespace SolverTrialStability

/-- Candidate and input indices are in fixed effective enumerations. The check
    includes timeout and output comparison against the true finite input. -/
def passes (check : Nat → Nat → Bool) (tests candidate : Nat) : Bool :=
  (List.range tests).all (check candidate)

def choose (check : Nat → Nat → Bool) (candidates tests : Nat) : Option Nat :=
  (List.range candidates).find? (passes check tests)

/-- A finite set of earlier failures has a common input bound. It need
    not be knowable from the code of the first globally correct candidate. -/
theorem finiteFailures (check : Nat → Nat → Bool) (k : Nat)
    (fails : ∀ i < k, ∃ x, check i x = false) :
    ∃ bound, ∀ i < k, ∃ x < bound, check i x = false := by
  induction k with
  | zero => exact ⟨0, by intro i hi; omega⟩
  | succ k ih =>
    obtain ⟨b,hb⟩ := ih (fun i hi => fails i (by omega))
    obtain ⟨y,hy⟩ := fails k (by omega)
    refine ⟨max b (y+1), ?_⟩
    intro i hi
    by_cases eq : i = k
    · subst i
      exact ⟨y,by omega,hy⟩
    · obtain ⟨x,hx,correct⟩ := hb i (by omega)
      exact ⟨x,by omega,correct⟩

/-- Beyond the bound, increasing either enumeration cannot change the first
    successful index. No test result is assumed for any later candidate. -/
theorem eventuallySelects (check : Nat → Nat → Bool) (k : Nat)
    (correct : ∀ x, check k x = true)
    (fails : ∀ i < k, ∃ x, check i x = false) :
    ∃ cutoff, ∀ candidates tests, k < candidates → cutoff ≤ tests →
      choose check candidates tests = some k := by
  obtain ⟨b,hb⟩ := finiteFailures check k fails
  refine ⟨b, ?_⟩
  intro candidates tests included enough
  apply List.find?_range_eq_some.2
  refine ⟨List.all_eq_true.2 (fun x _ => correct x), List.mem_range.2 included, ?_⟩
  intro i hi
  obtain ⟨x,hx,wrong⟩ := hb i hi
  have inRange : x ∈ List.range tests := List.mem_range.2 (by omega)
  cases yes : passes check tests i with
  | false => rfl
  | true =>
    have ok := (List.all_eq_true.1 yes) x inRange
    simp [wrong] at ok

end SolverTrialStability
