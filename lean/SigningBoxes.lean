import Std

namespace SigningBoxes

/-- The trit names the pair of live columns, in order AB, BC, CA. -/
inductive PairChoice where
  | ab | bc | ca
deriving DecidableEq, Repr

/-- The three bits encode the column-wise ratios of the two rows of signs. -/
def hits (a b c : Bool) : PairChoice → Bool
  | .ab => a != b
  | .bc => b != c
  | .ca => c != a

theorem misses_some (a b c : Bool) : ∃ j, hits a b c j = false := by
  cases a <;> cases b <;> cases c <;>
    first | exact ⟨.ab, rfl⟩ | exact ⟨.bc, rfl⟩ | exact ⟨.ca, rfl⟩

def signsMissing : PairChoice → Bool × Bool × Bool
  | .ab => (false, false, true)
  | .bc => (true, false, false)
  | .ca => (false, true, false)

theorem realize_box_coordinate (excluded input : PairChoice) :
    let r := signsMissing excluded
    hits r.1 r.2.1 r.2.2 input = decide (input ≠ excluded) := by
  cases excluded <;> cases input <;> decide

theorem realize_box {ι : Type} (excluded input : ι → PairChoice) :
    (∀ i, let r := signsMissing (excluded i)
          hits r.1 r.2.1 r.2.2 (input i) = true) ↔
    ∀ i, input i ≠ excluded i := by
  simp only [realize_box_coordinate, decide_eq_true_eq]

end SigningBoxes
