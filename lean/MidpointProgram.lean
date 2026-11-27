import Std

namespace MidpointProgram

/-- At a sufficiently wide ancestor containing the chosen interior point,
one of the two atom boundaries lies away from both ancestor edges. -/
theorem ancestorBoundary (left right low high point margin : Int)
    (positive : 0 ≤ margin)
    (inParent : left ≤ point ∧ point ≤ right)
    (atomInterior : low + 4*margin ≤ point ∧ point + 4*margin ≤ high)
    (parentWide : 2*(high-low) + 4*margin ≤ right-left) :
    (left + 2*margin ≤ low ∧ low + 2*margin ≤ right) ∨
    (left + 2*margin ≤ high ∧ high + 2*margin ≤ right) := by
  omega

/-- Empirical endpoints with guaranteed error cannot certify a spurious
boundary in a target cell. This includes true boundaries on its edges. -/
theorem conservativeBoundary (left right actual estimate err : Int)
    (accuracy : actual-err ≤ estimate ∧ estimate ≤ actual+err)
    (witness : left < estimate-err ∧ estimate+err < right) :
    left < actual ∧ actual < right := by omega

/-- The block read is forced when the true boundary has twice the error
in strict clearance in the current cell. -/
theorem boundaryDetected (left right actual estimate err : Int)
    (accuracy : actual-err ≤ estimate ∧ estimate ≤ actual+err)
    (clear : left + 2*err < actual ∧ actual + 2*err < right) :
    left < estimate-err ∧ estimate+err < right := by omega

/-- A final dyadic payload lying inside the atom with adequate slack passes
both endpoint tests on the good event. -/
theorem finalDetected (left right lo hi old new err : Int)
    (accuracy : lo-err ≤ old ∧ old ≤ lo+err ∧ hi-err ≤ new ∧ new ≤ hi+err)
    (clear : lo+2*err ≤ left ∧ right ≤ hi-2*err) :
    old+err ≤ left ∧ right ≤ new-err := by omega

/-- A binary search needs only an adjacent bracket of the *estimates*.
A monotone truth with an interior witness prevents this bracket from
jumping past the witness, even if the estimates oscillate. -/
theorem bracketBoundary (F E : Nat → Int) (base picked witness : Nat)
    (threshold right err : Int) (positive : 0 < err)
    (monotone : ∀ x y, x ≤ y → F x ≤ F y)
    (accurate : ∀ x, F x - err ≤ E x ∧ E x ≤ F x + err)
    (ordered : base ≤ witness)
    (bracket : picked = base ∨ E (picked - 1) < threshold)
    (high : threshold ≤ E picked)
    (inside : threshold + 4*err ≤ F witness ∧ F witness ≤ right - 8*err) :
    picked ≤ witness ∧
      threshold - 4*err < E picked - err ∧ E picked + err < right := by
  have lew : picked ≤ witness := by
    rcases bracket with eq | low
    · omega
    · by_cases later : witness < picked
      · have le : witness ≤ picked - 1 := by omega
        have inc := monotone _ _ le
        have lower := (accurate (picked - 1)).1
        omega
      · omega
  have inc := monotone _ _ lew
  have upper := (accurate picked).2
  omega

end MidpointProgram
