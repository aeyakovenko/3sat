import Std

/-! A row holds when the XOR of its occurrences is false. An affine
right-hand side may be included as a constant occurrence. Labels retain
provenance when a pairing certificate rearranges distinct occurrences. -/

namespace AffineRowPairs

inductive Key (Address : Type) where
  | memoryBit (address : Address) (bit : Nat)
  | constant (value : Bool)

structure Occurrence (Address Label : Type) where
  key : Key Address
  label : Label

def readKey (memory : Address → Nat → Bool) : Key Address → Bool
  | .memoryBit a bit => memory a bit
  | .constant b => b

def residual (memory : Address → Nat → Bool) : List (Occurrence Address Label) → Bool
  | [] => false
  | x :: xs => readKey memory x.key ^^ residual memory xs

theorem residualAppend (memory : Address → Nat → Bool)
    (xs ys : List (Occurrence Address Label)) :
    residual memory (xs ++ ys) = (residual memory xs ^^ residual memory ys) := by
  induction xs with
  | nil => simp [residual]
  | cons x xs ih => simp only [List.cons_append, residual, ih, Bool.xor_assoc]

theorem residualPerm (memory : Address → Nat → Bool) {xs ys : List (Occurrence Address Label)}
    (permutation : xs.Perm ys) : residual memory xs = residual memory ys := by
  induction permutation with
  | nil => rfl
  | cons x _ ih => simp only [residual, ih]
  | swap x y zs => exact Bool.xor_left_comm _ _ _
  | trans _ _ first second => exact first.trans second

/-- Position labels may differ; the two normalized memory keys or constants
have to agree. -/
def entries : List (Occurrence Address Label × Occurrence Address Label) →
    List (Occurrence Address Label)
  | [] => []
  | (x,y) :: ps => x :: y :: entries ps

theorem pairedEven (memory : Address → Nat → Bool)
    (pairs : List (Occurrence Address Label × Occurrence Address Label))
    (equalKeys : ∀ p ∈ pairs, p.1.key = p.2.key) :
    residual memory (entries pairs) = false := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨x,y⟩
    have eq : x.key = y.key := equalKeys _ List.mem_cons_self
    have tail := ih (fun p hp => equalKeys p (List.mem_cons_of_mem _ hp))
    simp only [entries, residual, eq, tail, Bool.xor_false, Bool.xor_self]

theorem satisfiedRowsEven (memory : Address → Nat → Bool)
    (sources : List (List (Occurrence Address Label)))
    (allHold : ∀ row ∈ sources, residual memory row = false) :
    residual memory sources.flatten = false := by
  induction sources with
  | nil => rfl
  | cons row rows ih =>
    have first := allHold row List.mem_cons_self
    have rest := ih (fun r hr => allHold r (List.mem_cons_of_mem _ hr))
    simp only [List.flatten_cons, residualAppend, first, rest, Bool.false_xor]

/-- A complete equal-key pairing of the target and all selected source
occurrences certifies the affine implication for every memory assignment.
The permutation prevents the certificate from dropping or reusing an
occurrence. The source list itself may contain repeated rows. -/
theorem pairedRowsImplyTarget (sources : List (List (Occurrence Address Label)))
    (target : List (Occurrence Address Label))
    (pairs : List (Occurrence Address Label × Occurrence Address Label))
    (permutation : (target ++ sources.flatten).Perm (entries pairs))
    (equalKeys : ∀ p ∈ pairs, p.1.key = p.2.key)
    (memory : Address → Nat → Bool)
    (allHold : ∀ row ∈ sources, residual memory row = false) :
    residual memory target = false := by
  have even := (residualPerm memory permutation).trans (pairedEven memory pairs equalKeys)
  simpa only [residualAppend, satisfiedRowsEven memory sources allHold, Bool.xor_false] using even

end AffineRowPairs
