import Std

namespace UnreadParityFirstHit

variable {Word : Type}

/-- Traverse exactly n edges without leaving an unresolved position. -/
def clearEnd (f : Word → Word) (unknown : Word → Bool) (x : Word) : Nat → Option Word
  | 0 => some x
  | n + 1 => if unknown x then none else clearEnd f unknown (f x) n

/-- Look for an unresolved position at distance at most n on the frozen orbit. -/
def firstWithin (f : Word → Word) (unknown : Word → Bool) (x : Word) : Nat → Option Word
  | 0 => if unknown x then some x else none
  | n + 1 => if unknown x then some x else firstWithin f unknown (f x) n

/-- The first unshadowed unknown hit at the end of a segment is determined by
its numerical origin, whatever the time labels of the individual loads. -/
theorem clear_hit (f : Word → Word) (unknown : Word → Bool) (x y : Word) (n : Nat)
    (clear : clearEnd f unknown x n = some y) (hit : unknown y = true) :
    firstWithin f unknown x n = some y := by
  induction n generalizing x with
  | zero =>
    have equal : x = y := Option.some.inj clear
    subst x
    simp [firstWithin, hit]
  | succ n ih =>
    cases atStart : unknown x with
    | false =>
      simpa [firstWithin, atStart] using ih (f x) (by simpa [clearEnd, atStart] using clear)
    | true => simp [clearEnd, atStart] at clear

theorem unique_hit (f : Word → Word) (unknown : Word → Bool) (x a b : Word) (i j : Nat)
    (left : firstWithin f unknown x i = some a)
    (right : firstWithin f unknown x j = some b) : a = b := by
  induction i generalizing x j with
  | zero =>
    cases hit : unknown x with
    | false => simp [firstWithin, hit] at left
    | true =>
      have xa : x = a := by simpa [firstWithin, hit] using left
      have xb : x = b := by cases j <;> simpa [firstWithin, hit] using right
      exact xa.symm.trans xb
  | succ i ih =>
    cases hit : unknown x with
    | true =>
      have xa : x = a := by simpa [firstWithin, hit] using left
      have xb : x = b := by cases j <;> simpa [firstWithin, hit] using right
      exact xa.symm.trans xb
    | false =>
      cases j with
      | zero => simp [firstWithin, hit] at right
      | succ j =>
        exact ih (f x) j (by simpa [firstWithin, hit] using left)
          (by simpa [firstWithin, hit] using right)

/-- Two segments can have different lengths and occur between different store
overrides. If their starts agree and both stop for an unresolved word, they
query the same physical address. -/
theorem same_origin_same_probe (f : Word → Word) (unknown : Word → Bool)
    (x a b : Word) (i j : Nat)
    (s : clearEnd f unknown x i = some a) (t : clearEnd f unknown x j = some b)
    (ha : unknown a = true) (hb : unknown b = true) : a = b :=
  unique_hit f unknown x a b i j (clear_hit f unknown x a i s ha)
    (clear_hit f unknown x b j t hb)

#print axioms same_origin_same_probe

end UnreadParityFirstHit
