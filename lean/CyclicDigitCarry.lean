import Std

namespace CyclicDigitCarry

def carryAt (x s low : Nat) : Nat :=
  if low ≤ x % low + s % low then 1 else 0

def digit (x low radix : Nat) := (x / low) % radix

/-- The full shifted digit is the independent digit sum plus the carry
computed on the untouched lower prefix. Works for any radix and position. -/
theorem shifted_digit (x s low radix : Nat) (h : 0 < low) :
    digit (x+s) low radix =
      ((digit x low radix + carryAt x s low) % radix + digit s low radix) % radix := by
  unfold digit carryAt
  rw [Nat.add_div h]
  simp only [Nat.mod_add_mod, Nat.add_mod_mod]
  congr 1
  omega

theorem bank_saving : 1540 > 3*22*23 := by decide

/-- Relative endpoint address filters telescope, including genuinely
nonzero initial filters. -/
theorem edge_differences (xs : List Int) (a b : Int) :
    let out := xs.foldl (fun pair u => (u, pair.2 + u - pair.1)) (a,b)
    out.2 - out.1 = b-a := by
  dsimp only
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    omega

#print axioms shifted_digit
#print axioms edge_differences

end CyclicDigitCarry
