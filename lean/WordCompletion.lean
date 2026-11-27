import Std

namespace WordCompletion

/-- Fill batches in their given order, truncating the first one that exhausts capacity. -/
def allocate (capacity : Nat) : List Nat → List Nat
  | [] => []
  | requested :: later =>
      min capacity requested :: allocate (capacity - requested) later

theorem allocated_sum (capacity : Nat) (requests : List Nat) :
    (allocate capacity requests).sum = min capacity requests.sum := by
  induction requests generalizing capacity with
  | nil => simp [allocate]
  | cons r rs ih =>
    simp only [allocate, List.sum_cons, ih]
    omega

theorem every_request (capacity : Nat) (requests : List Nat)
    (fits : requests.sum ≤ capacity) : allocate capacity requests = requests := by
  induction requests generalizing capacity with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.sum_cons] at fits
    simp only [allocate]
    rw [Nat.min_eq_right (by omega : r ≤ capacity), ih _ (by omega)]

/-- One incompletely paid batch forces exact exhaustion. Common denominator integer units. -/
theorem full_if_omitted {requests : List Nat} {capacity : Nat}
    (omitted : allocate capacity requests ≠ requests) :
    (allocate capacity requests).sum = capacity := by
  have h : ¬ requests.sum ≤ capacity := fun fit => omitted (every_request capacity requests fit)
  rw [allocated_sum, Nat.min_eq_left (by omega)]

theorem name_saving {m program d header parameter : Nat}
    (depth : program + d ≤ m) (spare : header + parameter < d) :
    header + parameter + program + (m - program - d) < m := by omega

/-- Finite form of the two averaging steps, using a common denominator. -/
theorem threshold_sum (entries : List Nat) (low high : Nat)
    (bound : ∀ n ∈ entries, n ≤ high) :
    entries.sum ≤ entries.length * low +
      (entries.filter (fun n => low < n)).length * high := by
  induction entries with
  | nil => simp
  | cons x xs ih =>
    have hx := bound x (by simp)
    have hs := ih (fun n hn => bound n (by simp [hn]))
    by_cases big : low < x
    · simp [List.filter_cons, big, Nat.succ_mul] <;> omega
    · simp [List.filter_cons, big, Nat.succ_mul] <;> omega

/-- A phase ledger lists incoming and spent credit on a common dyadic grid. -/
def ledger : List (Nat × Nat) → Nat → Nat → Prop
  | [], initial, final => initial = final
  | (incoming, spent) :: later, initial, final =>
      spent ≤ initial + incoming ∧ ledger later (initial + incoming - spent) final

theorem ledger_conservation (rows : List (Nat × Nat)) (initial final : Nat)
    (valid : ledger rows initial final) :
    initial + (rows.map Prod.fst).sum = final + (rows.map Prod.snd).sum := by
  induction rows generalizing initial with
  | nil => simpa [ledger] using valid
  | cons row rows ih =>
    obtain ⟨incoming, spent⟩ := row
    obtain ⟨enough, next⟩ := valid
    have rest := ih _ next
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Two schedules clearing at each phase boundary spend the same injected mass,
    even when they spend it in different windows. -/
theorem same_phase (left right : List (Nat × Nat)) (l : ledger left 0 0)
    (r : ledger right 0 0) (same : (left.map Prod.fst).sum = (right.map Prod.fst).sum) :
    (left.map Prod.snd).sum = (right.map Prod.snd).sum := by
  have hl := ledger_conservation left 0 0 l
  have hr := ledger_conservation right 0 0 r
  omega

end WordCompletion
