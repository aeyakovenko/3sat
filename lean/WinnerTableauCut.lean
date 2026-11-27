import Std

namespace WinnerTableauCut

variable {CPU Log Memory : Type}

/-- Keep the legal recorded operation on the cut edge itself. The controller at
    the following row switches to the idle return state. -/
def cpuAt (c : Nat → CPU) (idle : CPU) (cut t : Nat) : CPU :=
  if t ≤ cut then c t else idle

def logAt (ops : Nat → Log) (empty : Log) (cut t : Nat) : Log :=
  if t ≤ cut then ops t else empty

def memoryAt (m : Nat → Memory) (cut t : Nat) : Memory :=
  if t ≤ cut then m t else m (cut + 1)

/-- Every memory edge, including the cut, is honest. Every CPU edge except
    the cut is honest. This is sufficient for a complete memory-router witness. -/
theorem splice (cpu : Nat → CPU) (ops : Nat → Log) (mem : Nat → Memory)
    (idle : CPU) (empty : Log) (step : CPU → Log → CPU → Prop)
    (update : Memory → Log → Memory → Prop) (horizon cut : Nat) (atCut : cut < horizon)
    (trueStep : ∀ t < horizon, step (cpu t) (ops t) (cpu (t+1)))
    (trueMem : ∀ t < horizon, update (mem t) (ops t) (mem (t+1)))
    (idleStep : step idle empty idle) (noWrites : ∀ m, update m empty m) :
    let c := cpuAt cpu idle cut
    let o := logAt ops empty cut
    let m := memoryAt mem cut
    c 0 = cpu 0 ∧ c horizon = idle ∧ m 0 = mem 0 ∧
      (∀ t < horizon, update (m t) (o t) (m (t+1))) ∧
      (∀ t < horizon, t ≠ cut → step (c t) (o t) (c (t+1))) := by
  dsimp only
  refine ⟨by simp [cpuAt], by simp [cpuAt, Nat.not_le.mpr atCut], by simp [memoryAt], ?_, ?_⟩
  · intro t ht
    rcases Nat.lt_trichotomy t cut with before | equal | after
    · have next : t + 1 ≤ cut := by omega
      simpa [memoryAt, logAt, Nat.le_of_lt before, next] using trueMem t ht
    · subst t
      simpa [memoryAt, logAt] using trueMem cut ht
    · have next : ¬ t + 1 ≤ cut := by omega
      simp [memoryAt, logAt, Nat.not_le.mpr after, next, noWrites]
  · intro t ht different
    by_cases before : t < cut
    · have next : t + 1 ≤ cut := by omega
      simpa [cpuAt, logAt, Nat.le_of_lt before, next] using trueStep t ht
    · have now : ¬ t ≤ cut := by omega
      have next : ¬ t + 1 ≤ cut := by omega
      simp [cpuAt, logAt, now, next, idleStep]

private theorem cover_length (xs ys : List Nat) (distinct : xs.Nodup) (inside : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, remaining⟩ := List.nodup_cons.mp distinct
    have present := inside (List.mem_cons_self (a := x) (l := xs))
    have afterErase : xs ⊆ ys.erase x := by
      intro y mem
      have different : y ≠ x := fun eq => fresh (eq ▸ mem)
      exact (List.mem_erase_of_ne different).mpr (inside (List.mem_cons_of_mem x mem))
    have bound := ih (ys.erase x) remaining afterErase
    rw [List.length_erase_of_mem present] at bound
    have positive := List.length_pos_of_mem present
    simp only [List.length_cons]
    omega

/-- Every clause occurrence has at most one owner edge (use `horizon` for
    global axioms). The assignments may use different switch settings per cut. -/
theorem size_of_core {Clause Assignment : Type} (horizon : Nat) (owner : Clause → Nat)
    (satisfies : Assignment → Clause → Prop) (core : List Clause)
    (impossible : ¬∃ v, ∀ c ∈ core, satisfies v c)
    (repair : ∀ i < horizon, ∃ v, ∀ c ∈ core, owner c ≠ i → satisfies v c) :
    horizon ≤ core.length := by
  classical
  have covered : List.range horizon ⊆ core.map owner := by
    intro i inRange
    obtain ⟨v, ok⟩ := repair i (List.mem_range.mp inRange)
    apply Classical.byContradiction
    intro absent
    apply impossible
    refine ⟨v, ?_⟩
    intro c inCore
    exact ok c inCore (fun eq => absent (List.mem_map.mpr ⟨c, inCore, eq⟩))
  simpa using cover_length (List.range horizon) (core.map owner) List.nodup_range covered

end WinnerTableauCut
