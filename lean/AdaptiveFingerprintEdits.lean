import Std

namespace AdaptiveFingerprintEdits

/-- Every coordinate can have its own two possible contributions. -/
structure Cell where
  atZero : Bool
  atOne : Bool
  value : Bool
  leftMask : Bool
  rightMask : Bool

def contribution (c : Cell) (b : Bool) := if b then c.atOne else c.atZero

def parity (l : List Cell) (f : Cell → Bool) : Bool :=
  l.foldr (fun c a => f c ^^ a) false

def direction (c : Cell) (flag : Bool) := flag && (c.atZero ^^ c.atOne)

theorem difference (l : List Cell) :
    parity l (fun c => contribution c ((c.value ^^ c.leftMask) ^^ c.rightMask)) =
      ((parity l (fun c => contribution c c.value) ^^
        parity l (fun c => direction c c.leftMask)) ^^
        parity l (fun c => direction c c.rightMask)) := by
  induction l with
  | nil => rfl
  | cons c tail ih =>
    simp only [parity, List.foldr_cons] at ih ⊢
    rw [ih]
    generalize a : List.foldr _ false tail = u
    generalize b : List.foldr _ false tail = v
    generalize d : List.foldr _ false tail = w
    rcases c with ⟨z, o, x, left, right⟩
    cases z <;> cases o <;> cases x <;> cases left <;> cases right <;>
      cases u <;> cases v <;> cases w <;> rfl

theorem equal_signatures (l : List Cell)
    (eq : parity l (fun c => direction c c.leftMask) =
          parity l (fun c => direction c c.rightMask)) :
    parity l (fun c => contribution c ((c.value ^^ c.leftMask) ^^ c.rightMask)) =
      parity l (fun c => contribution c c.value) := by
  rw [difference, eq, Bool.xor_assoc]
  simp

/-- Replacing a summand in a fixed context does not require cancellation. -/
theorem replace_group {α : Type} (join : α → α → α) (outside left right : α)
    (same : left = right) : join outside left = join outside right := by
  rw [same]

/-- Moving one entry from a larger bucket to a smaller one reduces
the number of ordered collision pairs by exactly twice the remaining gap. -/
theorem rebalance (small gap : Nat) :
    let large := small + gap + 2
    let cost := fun n : Nat => n * (n - 1)
    cost large + cost small =
      cost (large - 1) + cost (small + 1) + 2 * (gap + 1) := by
  cases small <;> simp [Nat.succ_mul, Nat.mul_succ] <;> omega

end AdaptiveFingerprintEdits
