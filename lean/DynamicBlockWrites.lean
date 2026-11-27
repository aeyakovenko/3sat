import Std

namespace DynamicBlockWrites

/-- Writer blocks are ordered from the most recent to the earliest. -/
def latest {W : Type} : List (Option W) → Option W
  | [] => none
  | none :: xs => latest xs
  | some w :: _ => some w

theorem latest_none {W : Type} (xs : List (Option W)) :
    latest xs = none ↔ ∀ a ∈ xs, a = none := by
  induction xs with
  | nil => simp [latest]
  | cons head xs ih => cases head <;> simp [latest, ih]

theorem latest_some {W : Type} (xs : List (Option W)) (w : W) :
    latest xs = some w ↔ ∃ pre post, xs = pre ++ some w :: post ∧ ∀ a ∈ pre, a = none := by
  constructor
  · intro h
    induction xs with
    | nil => simp [latest] at h
    | cons head xs ih =>
      cases head with
      | none =>
        obtain ⟨pre, post, eq, absent⟩ := ih h
        refine ⟨none :: pre, post, ?_, ?_⟩
        · simp [eq]
        · simpa using absent
      | some value =>
        have equal : value = w := Option.some.inj h
        subst value
        exact ⟨[], xs, rfl, by simp⟩
  · rintro ⟨pre, post, rfl, absent⟩
    induction pre with
    | nil => rfl
    | cons a pre ih =>
      have ha := absent a (by simp)
      subst a
      exact ih (fun b hb => absent b (by simp [hb]))

/-- Sum equality detects all uncovered nonzero imports when each import has at most one owner. -/
theorem all_count_once (counts : List Nat) (capacity : ∀ a ∈ counts, a ≤ 1) :
    counts.sum = counts.length ↔ ∀ a ∈ counts, a = 1 := by
  have bound (xs : List Nat) (cap : ∀ a ∈ xs, a ≤ 1) : xs.sum ≤ xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := cap x (by simp)
      have tail := ih (fun a ha => cap a (by simp [ha]))
      simp only [List.sum_cons, List.length_cons]
      omega
  induction counts with
  | nil => simp
  | cons x xs ih =>
    have hx := capacity x (by simp)
    have cap := fun a (ha : a ∈ xs) => capacity a (by simp [ha])
    have tailBound := bound xs cap
    have tailIff := ih cap
    simp only [List.sum_cons, List.length_cons, List.forall_mem_cons]
    constructor
    · intro h
      exact ⟨by omega, tailIff.mp (by omega)⟩
    · rintro ⟨head, tail⟩
      have sum := tailIff.mpr tail
      omega

#print axioms latest_none
#print axioms latest_some
#print axioms all_count_once

end DynamicBlockWrites
