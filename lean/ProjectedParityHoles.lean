import Std

namespace ProjectedParityHoles

/-- Parity of the true entries in a finite list. -/
def odd : List Bool → Bool
  | [] => false
  | b :: rest => b ^^ odd rest

theorem odd_xor (a b : α → Bool) (xs : List α) :
    odd (xs.map (fun x => a x ^^ b x)) =
      (odd (xs.map a) ^^ odd (xs.map b)) := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    simp only [List.map_cons, odd, ih]
    cases a x <;> cases b x <;> cases odd (tail.map a) <;>
      cases odd (tail.map b) <;> decide

theorem correct_by_exceptions (approx witness : α → Bool) (xs : List α)
    (even : odd (xs.map approx) = false) :
    odd (xs.map (fun x => approx x ^^ witness x)) = odd (xs.map witness) := by
  rw [odd_xor, even]
  cases odd (xs.map witness) <;> decide

/-- The universal switch lets the same test certify all proposed holes,
regardless of the number of secondary witnesses for unrelated primaries. -/
theorem simultaneous_holes (H : α → Prop) (accepts : α → β → Prop)
    (rows : ι → α) [Nonempty β] :
    (∀ i y, H (rows i) ∧ ¬ accepts (rows i) y) ↔
      ∀ i, H (rows i) ∧ ¬ ∃ y, accepts (rows i) y := by
  constructor
  · intro check i
    obtain ⟨y⟩ := ‹Nonempty β›
    refine ⟨(check i y).1, ?_⟩
    rintro ⟨z, hz⟩
    exact (check i z).2 hz
  · intro check i y
    exact ⟨(check i).1, fun h => (check i).2 ⟨y, h⟩⟩

/-- A YES intersection remains YES after removal of an unprotected point. -/
theorem preserve_intersections (Q : ι → α → Prop) (W : α → Prop)
    (saved : ι → α) (u : α)
    (protect : ∀ i, (∃ x, Q i x ∧ W x) → Q i (saved i) ∧ W (saved i))
    (fresh : ∀ i, saved i ≠ u) (i : ι) :
    (∃ x, Q i x ∧ W x ∧ x ≠ u) ↔ (∃ x, Q i x ∧ W x) := by
  constructor
  · rintro ⟨x, hx, hw, _⟩
    exact ⟨x, hx, hw⟩
  · intro yes
    obtain ⟨hq, hw⟩ := protect i yes
    exact ⟨saved i, hq, hw, fresh i⟩

def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Normalizing a tagged self-dual majority gives the original AND. -/
theorem tagged_and (a b t : Bool) :
    (majority (a ^^ t) (b ^^ t) t ^^ t) = (a && b) := by
  cases a <;> cases b <;> cases t <;> decide

theorem tagged_or (a b t : Bool) :
    (majority (a ^^ t) (b ^^ t) (!t) ^^ t) = (a || b) := by
  cases a <;> cases b <;> cases t <;> decide

theorem tagged_pin (actual claim t : Bool) :
    ((!t) || ((actual ^^ t) == claim)) = ((!t) || (actual != claim)) := by
  cases actual <;> cases claim <;> cases t <;> decide

end ProjectedParityHoles
