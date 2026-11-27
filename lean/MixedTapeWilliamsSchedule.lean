import Std

namespace MixedTapeWilliamsSchedule
open Std.Internal

def slowdown : Rat := 541 / 500
def initialClock : Rat := 59 / 50
def outerInput : Rat := 1007 / 1000

def side (t : Rat) : Rat := 5*t/4 - 1
def space (t : Rat) : Rat := 2 * side t

/-- The base clock and two mixed conditional speedups. -/
def shortcut : Nat → Rat
  | 0 => 8/7
  | k+1 => (3 + shortcut k / slowdown) / (7/2)

/-- The crossing chart and the temporal table both have exponent one.
    The retained public input and private configurations fit the replay. -/
def admissible (t : Rat) : Prop :=
  t/4 ≤ side t ∧ side t ≤ t ∧ t/4 ≤ space t ∧ 0 ≤ space t ∧ space t ≤ 1 ∧
  t + t/4 - side t = 1 ∧ 1 ≤ t - (1-space t)

instance (t : Rat) : Decidable (admissible t) := by
  unfold admissible
  infer_instance

theorem shortcut_budgets :
    admissible (shortcut 0) ∧ admissible (shortcut 1) ∧ admissible (shortcut 2) ∧
    shortcut 0 - (1-space (shortcut 0)) = 1 ∧
    slowdown * (shortcut 1 - (1-space (shortcut 1))) = shortcut 0 ∧
    slowdown * (shortcut 2 - (1-space (shortcut 2))) = shortcut 1 := by decide

def firstSplit : Rat := outerInput - space initialClock
def secondSplit : Rat := 1 - space initialClock
def replay : Rat := initialClock - firstSplit - secondSplit

theorem outer_budgets :
    admissible initialClock ∧ 0 ≤ firstSplit ∧ 0 ≤ secondSplit ∧
    firstSplit + space initialClock = outerInput ∧
    secondSplit + space initialClock = 1 ∧ 1 ≤ replay ∧
    1 ≤ outerInput ∧ outerInput ≤ slowdown ∧
    slowdown * replay < shortcut 2 ∧
    slowdown * slowdown < outerInput * shortcut 2 ∧
    slowdown * slowdown * outerInput < initialClock := by decide

/-- The previously derived one-shortcut threshold does not cover this pair. -/
theorem beyond_single_iteration_limit :
    slowdown + 3 < (7/2)*slowdown*slowdown := by decide

end MixedTapeWilliamsSchedule
