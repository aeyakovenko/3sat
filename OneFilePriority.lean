import Std

namespace OneFilePriority

/-- After admission, a trigger is either already served or gets a winner of
    at least its priority. Smaller natural numbers have higher priority. -/
def PriorityAt (winner : Nat → Option Nat) (fires : Nat → Prop)
    (i admission : Nat) : Prop :=
  ∀ t, admission ≤ t → fires t →
    (∃ s, admission ≤ s ∧ s < t ∧ winner s = some i) ∨
      ∃ j, j ≤ i ∧ winner t = some j

private theorem count_distinct {xs pool : List Nat} (distinct : xs.Nodup)
    (inside : ∀ x ∈ xs, x ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have present := inside x (by simp)
    have positive := List.length_pos_of_mem present
    have shorter := ih tail (pool := pool.erase x) (by
      intro y hy
      have different : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne different).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem present] at shorter
    simp
    omega

/-- By one of any `i + 1` distinct triggering stages after admission, `i`
    has been selected. Only the smaller indices need a one-service guarantee. -/
theorem selected_by_trigger {winner : Nat → Option Nat} {fires : Nat → Prop}
    {i admission : Nat} (priority : PriorityAt winner fires i admission)
    (once : ∀ j < i, ∀ s t, winner s = some j → winner t = some j → s = t)
    (stages : List Nat) (distinct : stages.Nodup) (enough : i < stages.length)
    (active : ∀ t ∈ stages, admission ≤ t ∧ fires t) :
    ∃ t ∈ stages, ∃ s, admission ≤ s ∧ s ≤ t ∧ winner s = some i := by
  apply Classical.byContradiction
  intro never
  let blocker := fun t => (winner t).getD i
  have preempted : ∀ t ∈ stages, blocker t < i ∧ winner t = some (blocker t) := by
    intro t ht
    obtain ⟨admitted, triggered⟩ := active t ht
    rcases priority t admitted triggered with earlier | ⟨j, le, won⟩
    · obtain ⟨s, started, before, won⟩ := earlier
      exact False.elim (never ⟨t, ht, s, started, Nat.le_of_lt before, won⟩)
    · have different : j ≠ i := fun eq =>
        never ⟨t, ht, t, admitted, Nat.le_refl t, eq ▸ won⟩
      have lt : j < i := by omega
      simpa [blocker, won] using lt
  have distinctBlockers : (stages.map blocker).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ distinct
    intro s t hs ht different equalBlockers
    obtain ⟨lt, ws⟩ := preempted s hs
    have wt := (preempted t ht).2
    exact different (once _ lt s t ws (equalBlockers ▸ wt))
  have bounded := count_distinct (pool := List.range i) distinctBlockers (by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
    exact List.mem_range.mpr (preempted t ht).1)
  simp at bounded
  omega

private theorem triggering_stages {fires : Nat → Prop}
    (recurs : ∀ lo, ∃ t, lo ≤ t ∧ fires t) (count lo : Nat) :
    ∃ ts : List Nat, ts.length = count ∧ ts.Nodup ∧
      ∀ t ∈ ts, lo ≤ t ∧ fires t := by
  induction count generalizing lo with
  | zero => exact ⟨[], by simp⟩
  | succ n ih =>
    obtain ⟨t, low, trigger⟩ := recurs lo
    obtain ⟨ts, len, distinct, late⟩ := ih (t+1)
    refine ⟨t :: ts, by simp [len], List.nodup_cons.mpr ⟨?_, distinct⟩, ?_⟩
    · intro ht
      have := (late t ht).1
      omega
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨low, trigger⟩
      · obtain ⟨later, yes⟩ := late u hu
        exact ⟨by omega, yes⟩

/-- An obligation with triggers at unbounded stages eventually receives
    a file. Admission may occur arbitrarily late. -/
theorem selected_of_recurring {winner : Nat → Option Nat} {fires : Nat → Prop}
    {i admission : Nat} (priority : PriorityAt winner fires i admission)
    (once : ∀ j < i, ∀ s t, winner s = some j → winner t = some j → s = t)
    (recurs : ∀ lo, ∃ t, lo ≤ t ∧ fires t) :
    ∃ s, admission ≤ s ∧ winner s = some i := by
  obtain ⟨ts, len, distinct, active⟩ := triggering_stages recurs (i+1) admission
  obtain ⟨_, _, s, low, _, won⟩ :=
    selected_by_trigger priority once ts distinct (by omega) active
  exact ⟨s, low, won⟩

end OneFilePriority
