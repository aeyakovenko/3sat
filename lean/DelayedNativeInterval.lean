import Std

namespace DelayedNativeInterval

/-- Exact Boolean contradiction at the end of a deferred diagonalization. -/
theorem interval_mismatch (host rival : Nat → Bool) (start steps : Nat)
    (next : ∀ j, j < steps → host (start+j) = rival (start+(j+1)))
    (finish : host (start+steps) = !(rival start)) :
    ∃ j, j ≤ steps ∧ host (start+j) ≠ rival (start+j) := by
  apply Classical.byContradiction
  intro absent
  have eq : ∀ j, j ≤ steps → host (start+j) = rival (start+j) := by
    intro j hj
    apply Classical.byContradiction
    intro h
    exact absent ⟨j,hj,h⟩
  have constant : ∀ j, j ≤ steps → rival (start+j) = rival start := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have before : j < steps := by omega
      calc
        rival (start+(j+1)) = host (start+j) := (next j before).symm
        _ = rival (start+j) := eq j (by omega)
        _ = rival start := ih (by omega)
  have impossible : rival start = !(rival start) :=
    (constant steps (by omega)).symm.trans ((eq steps (by omega)).symm.trans finish)
  cases h : rival start <;> simp [h] at impossible

/-- A wrapper that returns the correct result on every timely output can
disagree only on the opposite sign from its fallback. -/
theorem price_at_disagreement (actual fallback fast : Bool)
    (diff : actual ≠ (if fast then actual else fallback)) :
    fast = false ∧ actual = !fallback := by
  cases fast <;> cases actual <;> cases fallback <;> simp_all

#print axioms interval_mismatch
#print axioms price_at_disagreement

end DelayedNativeInterval
