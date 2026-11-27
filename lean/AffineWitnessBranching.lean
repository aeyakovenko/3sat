import Std

namespace AffineWitnessBranching

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

/-- Budgets use saturated subtraction, so both children of a split at budget
    one have budget zero. A closed branch contributes no leaf to the cover. -/
inductive Tree : Nat → Type
  | closed {d} : Tree d
  | leaf {d} : Tree d
  | one {d} (child : Tree d) : Tree (d+1)
  | split {d} (left : Tree d) (right : Tree (d-1)) : Tree (d+1)

def leaves : {d : Nat} → Tree d → Nat
  | _, .closed => 0
  | _, .leaf => 1
  | _, .one child => leaves child
  | _, .split left right => leaves left + leaves right

private theorem fibStep (d : Nat) : fib d ≤ fib (d+1) := by
  cases d with
  | zero => decide
  | succ n => exact Nat.le_add_right _ _

private theorem oneLeaf (d : Nat) : 1 ≤ fib (d+2) := by
  induction d with
  | zero => decide
  | succ n ih => exact Nat.le_trans ih (fibStep (n+2))

theorem leafBound {d : Nat} (tree : Tree d) : leaves tree ≤ fib (d+2) := by
  induction tree with
  | closed => exact Nat.zero_le _
  | leaf => exact oneLeaf _
  | @one d child ih => exact Nat.le_trans ih (fibStep (d+2))
  | @split d left right ihLeft ihRight =>
    cases d with
    | zero => exact Nat.add_le_add ihLeft ihRight
    | succ n => exact Nat.add_le_add ihLeft ihRight

/-- Each forbidden pattern is the common solution to two affine bit equations
    when `l`, `m`, and `n` are themselves affine forms. -/
theorem productIffAvoids (l m n : Bool) :
    (l && m) = n ↔ ¬ (l = false ∧ n = true) ∧ ¬ (l = true ∧ (m ^^ n) = true) := by
  cases l <;> cases m <;> cases n <;> decide

abbrev Pair := Bool × Bool

private def points : List Pair :=
  [(false, false), (false, true), (true, false), (true, true)]

def character (u x : Pair) : Int :=
  if (u.1 && x.1) ^^ (u.2 && x.2) then -1 else 1

/-- Twenty-eight times the majorant for avoiding one tuple. -/
def weight28 (forbidden x : Pair) : Int := if x = forbidden then 24 else 28

def coefficient28 (forbidden u : Pair) : Int :=
  (points.map (fun x => weight28 forbidden x * character u x)).sum / 4

/-- This fixes the Fourier sign as well as each magnitude for every translate. -/
theorem majorantTransform (forbidden u : Pair) :
    coefficient28 forbidden u =
      (if u = (false, false) then 27 else -character u forbidden) := by
  obtain ⟨a,b⟩ := forbidden
  obtain ⟨i,j⟩ := u
  cases a <;> cases b <;> cases i <;> cases j <;> decide

/-- If `a³=27` and `b³=1` are the cube roots of the coefficient magnitudes
    of the scaled majorant, then the sum of their fourth powers is 84.
    Clearing denominators gives `‖ĝ‖_(4/3)^4=27/28` for the unscaled majorant. -/
theorem majorantNormIdentity : (3:Nat)^3 = 27 ∧
    3^4 + 1^4 + 1^4 + 1^4 = (84:Nat) ∧ 28 * 84^3 = 27 * (28:Nat)^4 := by
  decide

end AffineWitnessBranching
