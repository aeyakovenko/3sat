import Std

namespace ContractedStripSigns

abbrev F := Fin 3

/-- A present skip on a proper three-vertex path identifies consecutive increments. -/
theorem skip : ∀ a b c : F, a ≠ b → b ≠ c → (a ≠ c ↔ b-a = c-b) := by decide

def advance (a d : F) : Nat → F
  | 0 => a
  | n+1 => advance a d n + d

private theorem rotate_three : ∀ a d : F, ((a+d)+d)+d = a := by decide

theorem advance_three (a d : F) (n : Nat) :
    advance a d (n+3) = advance a d n := by
  exact rotate_three (advance a d n) d

theorem advance_three_multiple (a d : F) (n k : Nat) :
    advance a d (n+3*k) = advance a d n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show n+3*(k+1)=(n+3*k)+3 by omega, advance_three, ih]

theorem advance_six_multiple (a d : F) (n k : Nat) :
    advance a d (n+6*k) = advance a d n := by
  rw [show n+6*k=n+3*(2*k) by omega, advance_three_multiple]

theorem zero_displacement (a d : F) (k : Nat) : advance a d (3*k)=a := by
  simpa only [Nat.zero_add] using advance_three_multiple a d 0 k

theorem opposite_signs : ∀ d e : F, d ≠ 0 → e ≠ 0 → (d ≠ e ↔ d = 0-e) := by decide

end ContractedStripSigns
