import Std

/-! Per-lane arithmetic and the exact cross-count query invariant. -/

namespace AdaptiveWalkCounter

def bit (x : Bool) : Nat := if x then 1 else 0

theorem three_to_two (a b c : Bool) :
    bit a + bit b + bit c =
      bit ((a ^^ b) ^^ c) + 2 * bit ((a && b) || (a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

/-- A violation on a row is independent of the multiplicity of the visit. -/
theorem all_good_iff {Row Walk Column : Type} (selected : Walk → Row → Column)
    (good : Row → Column → Prop) (palette : Column → Column) :
    (∀ q i, good i (palette (selected q i))) ↔
      ∀ b i, (∃ q, selected q i = b) → good i (palette b) := by
  constructor
  · intro h b i hex
    obtain ⟨q, rfl⟩ := hex
    exact h q i
  · intro h q i
    exact h (selected q i) i ⟨q, rfl⟩

/-- In a stream starting empty, an insertion adds one mask and a compressor
removes one net mask; flushing also removes masks. -/
theorem compressor_count {inserted compressed flushed remaining : Nat}
    (accounting : inserted = compressed + flushed + remaining) :
    compressed ≤ inserted := by omega

#print axioms three_to_two
#print axioms all_good_iff
#print axioms compressor_count

end AdaptiveWalkCounter
