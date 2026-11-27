import Std

namespace CubicResetConstraints

def reset (incoming chordH chordG finalFlip : Bool) : Bool :=
  let first := incoming && chordH
  let second := first && chordG
  let third := second && !chordH
  third && (if finalFlip then !chordG else chordG)

theorem reset_zero (u h g flip : Bool) : reset u h g flip = false := by
  cases u <;> cases h <;> cases g <;> cases flip <;> decide

def negativeChain (s : Bool) : List Bool → Prop
  | [] => True
  | h :: hs => ∃ v : Bool, s = (v && !h) ∧ negativeChain v hs

theorem negative_init_false (hs : List Bool) : negativeChain false hs := by
  induction hs with
  | nil => trivial
  | cons h hs ih => exact ⟨false, rfl, ih⟩

theorem negative_init_true (hs : List Bool) :
    negativeChain true hs ↔ hs.any id = false := by
  induction hs with
  | nil => simp [negativeChain]
  | cons h hs ih =>
    cases h <;> simp [negativeChain, Bool.exists_bool, ih]

def positiveChain (hs : List Bool) := hs.any id

theorem variable_compatibility (positives negatives : List Bool) :
    negativeChain (positiveChain positives) negatives ↔
      ¬ (positives.any id = true ∧ negatives.any id = true) := by
  unfold positiveChain
  cases e : positives.any id
  · simp [negative_init_false]
  · rw [negative_init_true]
    cases negatives.any id <;> decide

theorem and_exception (a b : Bool) :
    ((a && b) != (!(a ^^ b))) = (!a && !b) := by
  cases a <;> cases b <;> decide

theorem or_exception (a b : Bool) :
    ((a || b) != (a ^^ b)) = (a && b) := by
  cases a <;> cases b <;> decide

theorem xor_insert (input h g : Bool) :
    ((((input ^^ h) ^^ g) ^^ h) ^^ g) = input := by
  cases input <;> cases h <;> cases g <;> decide

end CubicResetConstraints
