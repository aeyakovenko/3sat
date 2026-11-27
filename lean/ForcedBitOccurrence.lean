import Std

namespace ForcedBitOccurrence

inductive Tree where
  | leaf
  | branch (left right : Tree)
deriving DecidableEq

/-- Every leaf is at least the given distance below the root. -/
def Deep : Nat → Tree → Prop
  | 0, _ => True
  | _+1, .leaf => False
  | k+1, .branch l r => Deep k l ∧ Deep k r

/-- Count internal nodes both of whose children are leaves. -/
def cherries : Tree → Nat
  | .leaf => 0
  | .branch .leaf .leaf => 1
  | .branch l r => cherries l + cherries r

private theorem positive (t : Tree) (nonleaf : t ≠ .leaf) : 1 ≤ cherries t := by
  induction t with
  | leaf => exact False.elim (nonleaf rfl)
  | branch l r il ir =>
    cases l with
    | leaf =>
      cases r with
      | leaf => decide
      | branch a b =>
        simpa only [cherries, Nat.zero_add] using ir (by simp)
    | branch a b =>
      have left := il (by simp)
      cases r <;> simp only [cherries] <;> omega

private theorem split_bound (l r : Tree) :
    cherries l + cherries r ≤ cherries (.branch l r) := by
  cases l <;> cases r <;> simp [cherries]

/-- A deficiency-one tree whose leaves all have depth at least h+1
    has at least 2^h distinct cherry variables. -/
theorem deep_cherries (h : Nat) (t : Tree) (deep : Deep (h+1) t) :
    2^h ≤ cherries t := by
  induction h generalizing t with
  | zero =>
    cases t with
    | leaf => exact False.elim deep
    | branch l r => exact positive _ (by simp)
  | succ h ih =>
    cases t with
    | leaf => exact False.elim deep
    | branch l r =>
      obtain ⟨dl, dr⟩ := deep
      have hl := ih l dl
      have hr := ih r dr
      have hb := split_bound l r
      rw [Nat.pow_succ]
      omega

/-- Tarsi's inequality, the lost pinned occurrences, and the two
    degree-two witnesses in deficiency one force at least two excess
    occurrences in the original proper 3-CNF. -/
theorem excess_needed (rows vars d e lost : Nat)
    (tarsi : vars < rows)
    (inc : 3*rows + lost ≤ 3*vars + d + e)
    (cherries_if_one : rows = vars+1 → 2 ≤ lost) :
    5 ≤ d + e := by
  by_cases one : rows = vars+1
  · have := cherries_if_one one; omega
  · omega

def pinFive (h x y z : Bool) : Bool :=
  (h || x || z) && (h || !y || !z) && (h || !x || y) &&
  (x || y || !z) && (!x || !y || z)

def pinSix (h u v w p t : Bool) : Bool :=
  (h || !u || !v) && (h || u || w) && (h || u || !w) &&
  (!u || v || p) && (v || !p || t) && (v || !p || !t)

theorem pinFive_projection (h : Bool) :
    (∃ x y z, pinFive h x y z = true) ↔ h = true := by
  cases h <;> decide

theorem pinSix_projection (h : Bool) :
    (∃ u v w p t, pinSix h u v w p t = true) ↔ h = true := by
  cases h <;> decide

end ForcedBitOccurrence
