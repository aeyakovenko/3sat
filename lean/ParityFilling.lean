import Std

namespace ParityFilling

/-- Parity of the first n indexed bits. -/
def parity : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n+1, f => parity n f ^^ f n

private theorem interchange (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem parity_pair (n : Nat) (f g : Nat → Bool) :
    parity n (fun i => f i ^^ g i) = (parity n f ^^ parity n g) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [parity, ih]; exact interchange _ _ _ _

theorem parity_congr (n : Nat) (f g : Nat → Bool)
    (same : ∀ i, i < n → f i = g i) : parity n f = parity n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [parity]
    rw [ih (fun i hi => same i (by omega)), same n (by omega)]

theorem telescope (n : Nat) (v : Nat → Bool) :
    parity n (fun i => v i ^^ v (i+1)) = (v 0 ^^ v n) := by
  induction n with
  | zero => simp [parity]
  | succ n ih =>
    simp only [parity, ih]
    cases v 0 <;> cases v n <;> cases v (n+1) <;> decide

/-- Summing the local equations identifies the flux across a vertical cut.
    h is indexed by the gap between columns and then the row, and v by
    column and then the gap between rows. -/
theorem middle_cut (width height : Nat) (h v : Nat → Nat → Bool)
    (valid : ∀ i, i < width → ∀ j, j < height →
      (h i j ^^ h (i+1) j) = (v i j ^^ v i (j+1)))
    (left : parity height (h 0) = false)
    (top : ∀ i, i < width → v i height = false) :
    parity height (h width) = parity width (fun i => v i 0) := by
  have perColumn (i : Nat) (hi : i < width) :
      (parity height (h i) ^^ parity height (h (i+1))) = v i 0 := by
    rw [← parity_pair]
    rw [parity_congr height _ _ (valid i hi), telescope, top i hi, Bool.xor_false]
  have allColumns := parity_congr width _ _ perColumn
  rw [telescope, left, Bool.false_xor] at allColumns
  exact allColumns

end ParityFilling
