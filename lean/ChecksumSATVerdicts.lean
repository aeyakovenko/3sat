import Std

namespace ChecksumSATVerdicts

def andClauses (a b c : Bool) :=
  (!a || !b || c) && (a || !c) && (b || !c)

def xorClauses (a b c : Bool) :=
  (a || b || !c) && (a || !b || c) && (!a || b || c) && (!a || !b || !c)

theorem andGate : ∀ a b c, andClauses a b c = true ↔ c = (a && b) := by decide
theorem xorGate : ∀ a b c, xorClauses a b c = true ↔ c = (a ^^ b) := by decide

structure Slot where
  selector : Bool
  masked : Bool
  after : Bool
deriving DecidableEq

def fill (start : Bool) : List (Bool × Bool) → List Slot
  | [] => []
  | (coefficient, value) :: xs =>
    let masked := coefficient && value
    let next := start ^^ masked
    ⟨coefficient, masked, next⟩ :: fill next xs

def legal (start : Bool) : List (Bool × Bool) → List Slot → Prop
  | [], [] => True
  | (coefficient, value) :: xs, row :: rows =>
    row.selector = coefficient ∧ andClauses row.selector value row.masked = true ∧
      xorClauses start row.masked row.after = true ∧ legal row.after xs rows
  | _, _ => False

theorem unique_extension (xs : List (Bool × Bool)) (start : Bool) (rows : List Slot) :
    legal start xs rows ↔ rows = fill start xs := by
  induction xs generalizing start rows with
  | nil =>
    cases rows <;> simp [legal, fill]
  | cons x xs ih =>
    rcases x with ⟨coefficient, value⟩
    cases rows with
    | nil => simp [legal, fill]
    | cons row rows =>
      rcases row with ⟨s, m, t⟩
      simp only [legal, andGate, xorGate, ih, fill, List.cons.injEq, Slot.mk.injEq]
      constructor
      · rintro ⟨rfl,rfl,rfl,rfl⟩
        simp
      · rintro ⟨⟨rfl,rfl,rfl⟩,rfl⟩
        simp

def finish (start : Bool) : List Slot → Bool
  | [] => start
  | row :: rows => finish row.after rows

def bitSum : List (Bool × Bool) → Bool
  | [] => false
  | (c, h) :: xs => (c && h) ^^ bitSum xs

theorem final_value (xs : List (Bool × Bool)) (start : Bool) :
    finish start (fill start xs) = (start ^^ bitSum xs) := by
  induction xs generalizing start with
  | nil => simp [finish, fill, bitSum]
  | cons pair xs ih =>
    rcases pair with ⟨c,h⟩
    simp only [fill, finish, bitSum, ih, Bool.xor_assoc]

/-- Binary linear forms commute with the sparse outer-symbol sum. -/
def outer {K : Type} (zero : K) (add : K → K → K) : List (K × Bool) → K
  | [] => zero
  | (w,h) :: xs => if h then add w (outer zero add xs) else outer zero add xs

theorem checksum {K : Type} (zero : K) (add : K → K → K) (digit : K → Bool)
    (hzero : digit zero = false) (linear : ∀ a b, digit (add a b) = (digit a ^^ digit b))
    (rows : List (K × Bool)) :
    bitSum (rows.map fun row => (digit row.1, row.2)) = digit (outer zero add rows) := by
  induction rows with
  | nil => simp [bitSum, outer, hzero]
  | cons r rows ih =>
    rcases r with ⟨w,h⟩
    cases h <;> simp [bitSum, outer, ih, linear]

theorem pin_recovery : ∀ pin chk : Bool,
    (if decide (chk = pin) then pin else !pin) = chk := by decide

end ChecksumSATVerdicts
