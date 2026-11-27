import Std

namespace SingleCutTransfers

/-- The cut argument only needs the endpoint counts on the two sides. -/
theorem opposite_colors_large
    (m aL aR bL bR cutL cutR : Nat)
    (leftSide : aL + bL + cutL = m)
    (rightSide : aR + bR + cutR = m)
    (removed : 12 * (cutL + cutR) ≤ m)
    (red : 3 * (aL + aR) ≥ m)
    (blue : 3 * (bL + bR) ≥ m) :
    (6 * aL ≥ m ∧ 6 * bR ≥ m) ∨
      (6 * bL ≥ m ∧ 6 * aR ≥ m) := by
  omega

/-- A writer and reader separated by the middle phase cannot share a short
    interval, irrespective of the translated interval grid. -/
theorem no_short_internal_charge
    (side writer reader start width : Nat)
    (left : writer < side) (right : 3 * side ≤ reader)
    (small : width ≤ 2 * side) :
    ¬ (start ≤ writer ∧ reader < start + width) := by
  omega

def parity : List Bool → Bool
  | [] => false
  | x :: xs => x.xor (parity xs)

theorem pivotal (beforeBits suffix : List Bool) (x : Bool) :
    parity (beforeBits ++ ((!x) :: suffix)) = !(parity (beforeBits ++ (x :: suffix))) := by
  induction beforeBits with
  | nil =>
    cases x <;> cases h : parity suffix <;> simp [parity, h]
  | cons y ys ih =>
    simp only [List.cons_append, parity, ih]
    cases y <;> cases parity (ys ++ x :: suffix) <;> decide

theorem reorder_preserves_parity {xs ys : List Bool} (h : xs.Perm ys) :
    parity xs = parity ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [parity, ih]
  | swap x y rest =>
    simp only [parity]
    cases x <;> cases y <;> cases parity rest <;> decide
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- This list is the gain over four equally likely two-bit responses to a
    prediction for a payload whose forward entry was never exposed. -/
def nextStake (guess actual : Bool × Bool) (stake : Nat) : Nat :=
  if guess = actual then 4 * stake else 0

theorem fresh_offer_fair (guess : Bool × Bool) (stake : Nat) :
    nextStake guess (false, false) stake + nextStake guess (false, true) stake +
    nextStake guess (true, false) stake + nextStake guess (true, true) stake =
      4 * stake := by
  rcases guess with ⟨b, c⟩
  cases b <;> cases c <;> simp [nextStake]

/-- Per-coordinate sign identity splitting the lifted Walsh matrix. -/
theorem lifted_sign (x y i j : Bool) :
    ((x && y) ^^ (i && y) ^^ (x && j)) =
      (((x ^^ i) && (y ^^ j)) ^^ (i && j)) := by
  cases x <;> cases y <;> cases i <;> cases j <;> decide

theorem parity_pairwise (xs : List (Bool × Bool)) :
    parity (xs.map (fun p => p.1 ^^ p.2)) =
      (parity (xs.map Prod.fst) ^^ parity (xs.map Prod.snd)) := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    simp only [List.map_cons, parity, ih]
    cases a <;> cases b <;> cases parity (ps.map Prod.fst) <;>
      cases parity (ps.map Prod.snd) <;> decide

end SingleCutTransfers
