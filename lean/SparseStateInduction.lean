import Std

namespace SparseStateInduction

def parity {n : Nat} (bits : Fin n → Bool) : Bool :=
  (List.ofFn bits).foldl (fun a b => a ^^ b) false

def value {n : Nat} (leaf : List (Fin n) → Bool) :
    Nat → List (Fin n) → Bool
  | 0, path => leaf path
  | d+1, path => parity (fun i => value leaf d (i :: path))

/-- Claim all partial parities, then allow the challenger to select any
single subtable. Only the selected subtable has to appear on that play. -/
def certifies {n : Nat} (leaf : List (Fin n) → Bool) :
    Nat → List (Fin n) → Bool → Prop
  | 0, path, bit => bit = leaf path
  | d+1, path, bit => ∃ row : Fin n → Bool,
      parity row = bit ∧ ∀ i, certifies leaf d (i :: path) (row i)

theorem parityGameExact {n : Nat} (leaf : List (Fin n) → Bool) (d : Nat) :
    ∀ path bit, certifies leaf d path bit ↔ bit = value leaf d path := by
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro path bit
    constructor
    · rintro ⟨row, root, children⟩
      have honest : row = fun i => value leaf d (i :: path) :=
        funext fun i => (ih (i :: path) (row i)).mp (children i)
      simpa [value, honest] using root.symm
    · intro truth
      exact ⟨fun i => value leaf d (i :: path), truth.symm,
        fun i => (ih (i :: path) _).mpr rfl⟩

/-- The support may be chosen separately for every row and every boundary. -/
theorem localSupports {State Row : Type} (run : Nat → State)
    (holds : Nat → Row → State → Prop)
    (start : ∀ r, holds 0 r (run 0))
    (advance : ∀ i r, ∃ support : List Row,
      (∀ h ∈ support, holds i h (run i)) → holds (i+1) r (run (i+1))) :
    ∀ i r, holds i r (run i) := by
  intro i
  induction i with
  | zero => exact start
  | succ i ih =>
    intro r
    obtain ⟨support, proof⟩ := advance i r
    exact proof (fun h _ => ih h)

end SparseStateInduction
