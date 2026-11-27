import Std

namespace FirstFaultCache

/-- Previous writes are ordered newest first. -/
def current [DecidableEq Addr] (initial : Addr → Word) (a : Addr) :
    List (Addr × Word) → Word
  | [] => initial a
  | (b,v) :: rest => if b = a then v else current initial a rest

/-- A clean hash bucket has seen only writes of the respective initial words. -/
theorem clean_initial [DecidableEq Addr] (initial : Addr → Word)
    (bucket : Addr → Bucket) (a : Addr) (writes : List (Addr × Word))
    (clean : ∀ e ∈ writes, bucket e.1 = bucket a → e.2 = initial e.1) :
    current initial a writes = initial a := by
  induction writes with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨b,v⟩
    by_cases same : b = a
    · subst b
      simpa [current] using clean (a,v) (by simp) rfl
    · simp only [current, if_neg same]
      exact ih (fun e he => clean e (by simp [he]))

/-- With the same initial state the next request is determined by prior replies. -/
def stateAt (step : Nat → State → Word → State) (start : State)
    (replies : Nat → Word) : Nat → State
  | 0 => start
  | n+1 => step n (stateAt step start replies n) (replies n)

theorem common_prefix (step : Nat → State → Word → State) (start : State)
    (base trial : Nat → Word) (t : Nat) (prior : ∀ j, j < t → trial j = base j) :
    stateAt step start trial t = stateAt step start base t := by
  induction t with
  | zero => rfl
  | succ j ih =>
    simp only [stateAt]
    rw [ih (fun i hi => prior i (by omega)), prior j (by omega)]

theorem first_fault (step : Nat → State → Word → State) (start : State)
    (base trial : Nat → Word) (k : Nat)
    (different : stateAt step start trial k ≠ stateAt step start base k) :
    ∃ t, t < k ∧ trial t ≠ base t ∧ (∀ j, j < t → trial j = base j) ∧
      stateAt step start trial t = stateAt step start base t := by
  classical
  have first (m : Nat) (exists_bad : ∃ j, j < m ∧ trial j ≠ base j) :
      ∃ j, j < m ∧ trial j ≠ base j ∧ ∀ i, i < j → trial i = base i := by
    induction m with
    | zero => obtain ⟨j,hj,_⟩ := exists_bad; omega
    | succ m ih =>
      by_cases earlier : ∃ i, i < m ∧ trial i ≠ base i
      · obtain ⟨i,hi,bad,prior⟩ := ih earlier
        exact ⟨i, by omega, bad, prior⟩
      · obtain ⟨j,hj,bad⟩ := exists_bad
        have eq : j = m := by
          apply Classical.byContradiction
          intro distinct
          exact earlier ⟨j, by omega, bad⟩
        subst j
        refine ⟨m, by omega, bad, ?_⟩
        exact fun i hi => Classical.byContradiction fun unequal => earlier ⟨i, hi, unequal⟩
  have need : ∃ j, j < k ∧ trial j ≠ base j := by
    apply Classical.byContradiction
    intro none
    apply different (common_prefix step start base trial k ?_)
    exact fun j hj => Classical.byContradiction fun unequal => none ⟨j, hj, unequal⟩
  obtain ⟨t,ht,bad,prior⟩ := first k need
  exact ⟨t, ht, bad, prior, common_prefix step start base trial t prior⟩

end FirstFaultCache
