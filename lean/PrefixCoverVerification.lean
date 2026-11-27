import Std

namespace PrefixCoverVerification

structure BitComparison where
  actual : Bool
  predicted : Bool
  center : Bool

def gap (a b : Bool) : Nat := if a == b then 0 else 1

def distance (xs : List BitComparison) (a b : BitComparison → Bool) : Nat :=
  (xs.map (fun v => gap (a v) (b v))).sum

theorem coordinate_gap (v : BitComparison)
    (probe : v.predicted ≠ v.center → v.actual = v.predicted) :
    gap v.actual v.center = gap v.predicted v.center + gap v.actual v.predicted := by
  rcases v with ⟨a, p, c⟩
  cases a <;> cases p <;> cases c <;> simp_all [gap]

open BitComparison in
theorem checked_distance (xs : List BitComparison)
    (probes : ∀ v ∈ xs, v.predicted ≠ v.center → v.actual = v.predicted) :
    distance xs actual center =
      distance xs predicted center + distance xs actual predicted := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    have tail := ih (fun z hz => probes z (List.mem_cons_of_mem _ hz))
    have head := coordinate_gap v (probes _ (by simp))
    simp only [distance, List.map_cons, List.sum_cons] at *
    omega

open BitComparison in
theorem no_hidden_mismatch (xs : List BitComparison)
    (probes : ∀ v ∈ xs, v.predicted ≠ v.center → v.actual = v.predicted)
    (count : distance xs actual center = distance xs predicted center) :
    distance xs actual predicted = 0 := by
  have add := checked_distance xs probes
  omega

end PrefixCoverVerification
