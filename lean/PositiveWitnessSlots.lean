import Std

namespace PositiveWitnessSlots

/-- A bit printed before the terminal cursor lies in some checkpoint interval,
    including when intervening segments produce no bits. -/
theorem cursor_exists (cursor : Nat → Nat) (start : cursor 0 = 0)
    (target segments : Nat) (printed : target < cursor segments) :
    ∃ i, i < segments ∧ cursor i ≤ target ∧ target < cursor (i + 1) := by
  induction segments with
  | zero => omega
  | succ n ih =>
    by_cases prior : target < cursor n
    · obtain ⟨i, before, lo, hi⟩ := ih prior
      exact ⟨i, by omega, lo, hi⟩
    · exact ⟨n, by omega, by omega, printed⟩

/-- With genuine nondecreasing cursors the interval identifying a particular bit is unique. -/
theorem cursor_unique (cursor : Nat → Nat) (increases : ∀ a b, a ≤ b → cursor a ≤ cursor b)
    {i j target : Nat} (ilo : cursor i ≤ target) (ihi : target < cursor (i + 1))
    (jlo : cursor j ≤ target) (jhi : target < cursor (j + 1)) : i = j := by
  by_cases lt : i < j
  · have le := increases (i+1) j (by omega)
    omega
  · by_cases gt : j < i
    · have le := increases (j+1) i (by omega)
      omega
    · omega

/-- Distinct slots of the right total length, all with in-range names, fill the palette. -/
theorem slot_names_cover (names palette : List Nat) (distinct : names.Nodup)
    (within : ∀ x ∈ names, x ∈ palette) (same : names.length = palette.length) :
    names.Perm palette := by
  induction names generalizing palette with
  | nil => cases palette <;> simp_all
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have member := within x (by simp)
    have shorter : xs.length = (palette.erase x).length := by
      rw [List.length_erase_of_mem member]
      simp only [List.length_cons] at same
      omega
    have withinTail : ∀ y ∈ xs, y ∈ palette.erase x := by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).2 (within y (by simp [hy]))
    exact ((ih _ tail withinTail shorter).cons x).trans (List.perm_cons_erase member).symm

structure Literal (Name : Type) where
  name : Name
  polarity : Bool

/-- A violated clause is witnessed by three named slots, even with repeated literals.
    The slot order and the relative positions of these slots are unrestricted. -/
theorem clause_defect_iff {Name Slot : Type} (name : Slot → Name) (value : Slot → Bool)
    (assignment : Name → Bool) (covered : ∀ a, ∃ s, name s = a)
    (consistent : ∀ s, value s = assignment (name s)) (a b c : Literal Name) :
    (∃ i j k, name i = a.name ∧ name j = b.name ∧ name k = c.name ∧
      value i ≠ a.polarity ∧ value j ≠ b.polarity ∧ value k ≠ c.polarity) ↔
    ¬(assignment a.name = a.polarity ∨ assignment b.name = b.polarity ∨
      assignment c.name = c.polarity) := by
  constructor
  · rintro ⟨i, j, k, ai, bj, ck, x, y, z⟩
    rw [consistent i, ai] at x
    rw [consistent j, bj] at y
    rw [consistent k, ck] at z
    rintro (sat | sat | sat)
    · exact x sat
    · exact y sat
    · exact z sat
  · intro bad
    obtain ⟨i, ai⟩ := covered a.name
    obtain ⟨j, bj⟩ := covered b.name
    obtain ⟨k, ck⟩ := covered c.name
    refine ⟨i, j, k, ai, bj, ck, ?_, ?_, ?_⟩
    · rw [consistent i, ai]
      exact fun sat => bad (.inl sat)
    · rw [consistent j, bj]
      exact fun sat => bad (.inr (.inl sat))
    · rw [consistent k, ck]
      exact fun sat => bad (.inr (.inr sat))

/-- In an unambiguous trace relation, pinning the result retains exactly one witness
    if the bit agrees and excludes every witness otherwise. -/
theorem pinned_unique_iff {W : Type} (valid : W → Prop) (real : W)
    (sole : ∀ w, valid w ↔ w = real) (output : W → Bool) (pin : Bool) :
    (∃ w, (valid w ∧ output w = pin) ∧ ∀ z, valid z ∧ output z = pin → z = w) ↔
      output real = pin := by
  constructor
  · rintro ⟨w, ⟨hw, bit⟩, _⟩
    simpa [(sole w).1 hw] using bit
  · intro bit
    exact ⟨real, ⟨(sole real).2 rfl, bit⟩, fun z hz => (sole z).1 hz.1⟩

/-- A third data bit supplies both polarities of the padding literal in each
    implication, enforcing equality without adding variables to the assignment. -/
theorem four_clauses_copy (y z w : Bool) :
    (((!y || z || w) && (!y || z || !w) &&
      (y || !z || w) && (y || !z || !w)) = true) ↔ y = z := by
  cases y <;> cases z <;> cases w <;> decide

end PositiveWitnessSlots
