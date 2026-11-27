import Std

namespace LruReuseDistance

variable {α : Type} [DecidableEq α]

/-- The capacity-limited cache step, with the most recent address first. -/
def access (k : Nat) (cache : List α) (a : α) : List α :=
  (a :: cache.erase a).take k

/-- The actual online algorithm, with its input in chronological order. -/
def run (k : Nat) (events : List α) : List α := events.foldl (access k) []

/-- In this auxiliary representation the *input* is newest first. -/
def stack : List α → List α
  | [] => []
  | a :: xs => a :: (stack xs).erase a

theorem stack_nodup (xs : List α) : (stack xs).Nodup := by
  induction xs with
  | nil => simp [stack]
  | cons a xs ih =>
    exact List.nodup_cons.mpr ⟨ih.not_mem_erase, ih.erase a⟩

theorem mem_stack (a : α) (xs : List α) : a ∈ stack xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp [stack]
  | cons x xs ih =>
    by_cases h : a = x
    · simp [stack, h]
    · simp [stack, h, List.mem_erase_of_ne h, ih]

private theorem take_erase_take (k : Nat) (xs : List α) (a : α) :
    ((xs.take (k+1)).erase a).take k = (xs.erase a).take k := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      by_cases h : x = a
      · simp [h, List.take_take]
      · simp [List.take_succ_cons, List.erase_cons, h, ih]

/-- Evicting the previous tail eagerly gives exactly the same next cache. -/
theorem access_take (k : Nat) (xs : List α) (a : α) :
    access k (xs.take k) a = access k xs a := by
  cases k with
  | zero => simp [access]
  | succ k => simp [access, take_erase_take]

private theorem foldr_eq_take_stack (k : Nat) (xs : List α) :
    xs.foldr (fun a c => access k c a) [] = (stack xs).take k := by
  induction xs with
  | nil => simp [stack]
  | cons a xs ih =>
    simp only [List.foldr_cons, ih, access_take]
    rfl

theorem run_eq_take_stack (k : Nat) (events : List α) :
    run k events = (stack events.reverse).take k := by
  rw [run, List.foldl_eq_foldr_reverse, foldr_eq_take_stack]

/-- Stop just before the first occurrence in newest-first order. -/
def since (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then [] else x :: since a xs

theorem not_mem_since (a : α) (xs : List α) : a ∉ since a xs := by
  induction xs with
  | nil => simp [since]
  | cons x xs ih =>
    by_cases h : x = a <;> simp [since, h, Ne.symm, ih, *]

private theorem split_since {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ older, xs = since a xs ++ a :: older := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x = a
    · subst x
      exact ⟨xs, by simp [since]⟩
    · obtain ⟨older, p⟩ := ih (by simpa [Ne.symm hx] using h)
      exact ⟨older, by simpa [since, hx] using congrArg (List.cons x) p⟩

/-- Addresses more recent than the marked occurrence occupy precisely the
front of the full stack, independently of all earlier events. -/
theorem split_stack (a : α) (newer older : List α) (ha : a ∉ newer) :
    ∃ rest, stack (newer ++ a :: older) = stack newer ++ a :: rest := by
  induction newer with
  | nil => exact ⟨(stack older).erase a, rfl⟩
  | cons x newer ih =>
    obtain ⟨hax, hab⟩ : a ≠ x ∧ a ∉ newer := by simpa using ha
    obtain ⟨rest, hr⟩ := ih hab
    by_cases hx : x ∈ stack newer
    · refine ⟨rest, ?_⟩
      simp only [List.cons_append, stack]
      rw [hr, List.erase_append_left _ hx]
    · refine ⟨rest.erase x, ?_⟩
      simp only [List.cons_append, stack]
      rw [hr, List.erase_append_right _ hx, List.erase_of_not_mem hx,
        List.erase_cons_tail (by simpa using hax)]

omit [DecidableEq α] in
private theorem mem_take_at (k : Nat) (a : α) (newer older : List α)
    (h : a ∉ newer) :
    a ∈ (newer ++ a :: older).take k ↔ newer.length < k := by
  induction newer generalizing k with
  | nil => cases k <;> simp
  | cons x newer ih =>
    obtain ⟨hx, hn⟩ : a ≠ x ∧ a ∉ newer := by simpa using h
    cases k with
    | zero => simp
    | succ k => simpa [hx] using ih k hn

/-- Number of distinct intervening addresses since the last visit. Membership
is checked separately in the theorem, so a never-seen address is always cold.
`stack_nodup` and `mem_stack` certify the distinct-address count. -/
def reuseDistance (a : α) (events : List α) : Nat :=
  (stack (since a events.reverse)).length

/-- For every finite chronological trace, every address and every capacity,
including zero, characterize the state computed by the operational cache. -/
theorem resident_iff (k : Nat) (events : List α) (a : α) :
    a ∈ run k events ↔ a ∈ events ∧ reuseDistance a events < k := by
  rw [run_eq_take_stack]
  by_cases ha : a ∈ events
  · have hr : a ∈ events.reverse := by simpa using ha
    obtain ⟨older, split⟩ := split_since hr
    have sn := not_mem_since a events.reverse
    obtain ⟨rest, hs⟩ := split_stack a _ older sn
    have hn : a ∉ stack (since a events.reverse) := by simpa [mem_stack] using sn
    have hshape : stack events.reverse = stack (since a events.reverse) ++ a :: rest :=
      (congrArg stack split).trans hs
    rw [hshape, mem_take_at _ _ _ _ hn]
    simp [reuseDistance, ha]
  · have hn : a ∉ stack events.reverse := by simpa [mem_stack] using ha
    exact iff_of_false (fun h => hn (List.mem_of_mem_take h)) (fun h => ha h.1)

end LruReuseDistance
