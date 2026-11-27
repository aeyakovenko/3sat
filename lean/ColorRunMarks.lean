import Std

namespace ColorRunMarks

/-- The marks in one ordered segment touch its left or right endpoint. -/
def covered (left right i : Nat) : Prop := i < left ∨ right ≤ i

theorem add_left (left right endpoint i : Nat) :
    covered left right i ∨ i < endpoint ↔ covered (max left endpoint) right i := by
  unfold covered
  omega

theorem add_right (left right endpoint i : Nat) :
    covered left right i ∨ endpoint ≤ i ↔ covered left (min right endpoint) i := by
  unfold covered
  omega

/-- Before modular reduction, composing the two reflections produces the
    stride translation. The polynomial identity descends modulo every Q. -/
theorem reflection_pair (c p : Int) : c - (0 - p) = p + c := by omega

end ColorRunMarks
