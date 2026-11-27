import Std

namespace ConditionalCompletionCode

/-- A partial overwrite, with possibly infinite index and value types. -/
def splice {ι α : Type} (takeFixed : ι → Bool) (fixed other : ι → α) (i : ι) : α :=
  if takeFixed i then fixed i else other i

/-- This hypothesis is supplied by interpolation on at least the dimension many points. -/
def Determines {ι α : Type} (code : (ι → α) → Prop) (chosen : ι → Bool) : Prop :=
  ∀ x y, code x → code y → (∀ i, chosen i = true → x i = y i) → x = y

/-- If an interpolant exists on the prescribed coordinates, one equality predicate remains. -/
theorem splice_iff {ι α : Type} (code : (ι → α) → Prop) (chosen : ι → Bool)
    (fixed other candidate : ι → α) (unique : Determines code chosen)
    (valid : code candidate) (fits : ∀ i, chosen i = true → fixed i = candidate i) :
    code (splice chosen fixed other) ↔ ∀ i, chosen i = false → other i = candidate i := by
  constructor
  · intro accepted
    have eq := unique _ _ accepted valid (fun i hi => by simpa [splice, hi] using fits i hi)
    intro i hi
    simpa [splice, hi] using congrFun eq i
  · intro check
    have eq : splice chosen fixed other = candidate := by
      funext i
      cases hi : chosen i with
      | true => simpa [splice, hi] using fits i hi
      | false => simpa [splice, hi] using check i hi
    simpa only [eq] using valid

/-- Inconsistent prescribed coordinates defeat every completion. -/
theorem no_interpolant {ι α : Type} (code : (ι → α) → Prop) (chosen : ι → Bool)
    (fixed other : ι → α)
    (noneFit : ¬ ∃ x, code x ∧ ∀ i, chosen i = true → x i = fixed i) :
    ¬ code (splice chosen fixed other) := by
  intro h
  exact noneFit ⟨_, h, fun i hi => by simp [splice, hi]⟩

end ConditionalCompletionCode
