import Std

namespace ImplicitAssignmentAdvice

/-- Remaining depth, then the binary prefix as an integer. -/
def live (bad : Nat → Bool) : Nat → Nat → Bool
  | 0, p => bad p
  | d+1, p => live bad d (2*p) || live bad d (2*p+1)

/-- A row is asked only about the left child. Even a dishonest row returns a leaf. -/
def descend (row : Nat → Nat → Bool) : Nat → Nat → Nat
  | 0, p => p
  | d+1, p =>
    if row d (2*p) then descend row d (2*p)
    else descend row d (2*p+1)

theorem valid_of_live (bad : Nat → Bool) (d p : Nat) :
    live bad d p = true → bad (descend (live bad) d p) = true := by
  induction d generalizing p with
  | zero => exact id
  | succ d ih =>
    intro h
    by_cases hl : live bad d (2*p) = true
    · simpa [descend, hl] using ih (2*p) hl
    · have hr : live bad d (2*p+1) = true := by simpa [live, hl] using h
      simpa [descend, hl] using ih (2*p+1) hr

theorem live_of_valid (bad : Nat → Bool) (row : Nat → Nat → Bool) (d p : Nat) :
    bad (descend row d p) = true → live bad d p = true := by
  induction d generalizing p with
  | zero => exact id
  | succ d ih =>
    by_cases hl : row d (2*p) = true
    · intro h
      have hh : bad (descend row d (2*p)) = true := by simpa [descend, hl] using h
      simp [live, ih (2*p) hh]
    · intro h
      have hh : bad (descend row d (2*p+1)) = true := by simpa [descend, hl] using h
      simp [live, ih (2*p+1) hh]

def findBad (bad : Nat → Bool) (rows : List (Nat → Nat → Bool)) (d : Nat) : Bool :=
  rows.any fun row => bad (descend row d 0)

theorem findBad_iff (bad : Nat → Bool) (rows : List (Nat → Nat → Bool))
    (good : live bad ∈ rows) (d : Nat) :
    findBad bad rows d = true ↔ live bad d 0 = true := by
  constructor
  · intro found
    obtain ⟨row, _, ok⟩ := List.any_eq_true.mp found
    exact live_of_valid bad row d 0 ok
  · intro h
    exact List.any_eq_true.mpr ⟨live bad, good, valid_of_live bad d 0 h⟩

/-- The correct comparison row singles out the least satisfying word. -/
theorem least_filter (model : Nat → Prop) (z : Nat) (hz : model z)
    (least : ∀ y, model y → z ≤ y) (x : Nat) :
    (model x ∧ ¬∃ y, model y ∧ y < x) ↔ x = z := by
  constructor
  · intro ⟨hx, h⟩
    have lower := least x hx
    have upper : ¬ z < x := fun hlt => h ⟨z, hz, hlt⟩
    omega
  · rintro rfl
    exact ⟨hz, fun ⟨y, hy, hlt⟩ => Nat.not_lt_of_ge (least y hy) hlt⟩

theorem bit_of_unique {index : Type} (bit : Nat → index → Prop)
    (passing : Nat → Prop) (z : Nat) (unique : ∀ x, passing x ↔ x = z) (i : index) :
    (∃ x, passing x ∧ bit x i) ↔ bit z i := by
  constructor
  · rintro ⟨x, hx, hi⟩
    rwa [← (unique x).mp hx]
  · exact fun hz => ⟨z, (unique z).mpr rfl, hz⟩

/-- Some candidate implicit assignment satisfies the formula exactly on YES files.
The false-clause oracle is implemented by the prefix descent, independently per row. -/
theorem portfolio_iff {α : Type} (candidates : List α)
    (bad : α → Nat → Bool) (menu : α → List (Nat → Nat → Bool)) (d : Nat)
    (sat : Prop) (truth : ∀ a ∈ candidates, live (bad a) ∈ menu a)
    (models : sat ↔ ∃ a ∈ candidates, live (bad a) d 0 = false) :
    (candidates.any fun a => !findBad (bad a) (menu a) d) = true ↔ sat := by
  constructor
  · intro success
    obtain ⟨a, mem, survived⟩ := List.any_eq_true.mp success
    apply models.mpr
    refine ⟨a, mem, ?_⟩
    cases hl : live (bad a) d 0 with
    | false => rfl
    | true =>
      have found := (findBad_iff (bad a) (menu a) (truth a mem) d).mpr hl
      simp [found] at survived
  · intro h
    obtain ⟨a, mem, noBad⟩ := models.mp h
    apply List.any_eq_true.mpr
    refine ⟨a, mem, ?_⟩
    cases found : findBad (bad a) (menu a) d with
    | false => rfl
    | true =>
      have hl := (findBad_iff (bad a) (menu a) (truth a mem) d).mp found
      simp [noBad] at hl

/-- In the bounded-ambiguity variant an increasing selection from the canonical
model list is a sublist. At the exact census even its first member is forced. -/
theorem census_filter {α : Type} (models : List α) (test : List α → Prop) :
    (∃ xs, xs.Sublist models ∧ xs.length = models.length ∧ test xs) ↔ test models := by
  constructor
  · rintro ⟨xs, sub, len, ok⟩
    simpa [sub.eq_of_length len] using ok
  · exact fun ok => ⟨models, List.Sublist.refl _, rfl, ok⟩

end ImplicitAssignmentAdvice
