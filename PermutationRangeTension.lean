import Std

/-!
A blue edge is given by a left endpoint and its length. Taking these pairs
from the adjacent entries of a permutation gives the two-path colouring problem.
Every sum and product in the interval equations is in the field with three elements.
-/
namespace PermutationRangeTension

abbrev F := Fin 3

def interval (gap : Nat → F) (left : Nat) : Nat → F
  | 0 => 0
  | d + 1 => interval gap left d + (1 + gap (left + d))

def gapsOf (h : Nat → F) (i : Nat) : F := h (i + 1) - h i - 1

private theorem selfDiff : ∀ a : F, a - a = 0 := by decide
private theorem extendDiff : ∀ a b c : F,
    (b - a) + (1 + (c - b - 1)) = c - a := by decide

theorem telescope (h : Nat → F) (left d : Nat) :
    interval (gapsOf h) left d = h (left + d) - h left := by
  induction d with
  | zero => simp [interval, selfDiff]
  | succ d ih =>
    change interval (gapsOf h) left d + (1 + (h ((left + d) + 1) - h (left + d) - 1))
      = h ((left + d) + 1) - h left
    rw [ih, extendDiff]

def colorsOf (gap : Nat → F) (i : Nat) : F := interval gap 0 i

private theorem recoverStep : ∀ a b : F, a + (1 + b) - a - 1 = b := by decide

theorem recoveredGaps (gap : Nat → F) : gapsOf (colorsOf gap) = gap := by
  funext i
  simp [gapsOf, colorsOf, interval, recoverStep]

private theorem legalGap : ∀ a b : F,
    (b - a - 1) * (b - a - 1) = b - a - 1 ↔ a ≠ b := by decide

private theorem legalRange : ∀ a b : F,
    (b - a) * (b - a) = 1 ↔ a ≠ b := by decide

def twoPathColouring (n : Nat) (blue : Nat → Nat → Prop) (h : Nat → F) : Prop :=
  (∀ i, i + 1 < n → h i ≠ h (i + 1)) ∧
  (∀ l d, l + d < n → blue l d → h l ≠ h (l + d))

def intervalEquations (n : Nat) (blue : Nat → Nat → Prop) (gap : Nat → F) : Prop :=
  (∀ i, i + 1 < n → gap i * gap i = gap i) ∧
  (∀ l d, l + d < n → blue l d → interval gap l d * interval gap l d = 1)

theorem equationsOfGaps (n : Nat) (blue : Nat → Nat → Prop) (h : Nat → F) :
    intervalEquations n blue (gapsOf h) ↔ twoPathColouring n blue h := by
  simp only [intervalEquations, twoPathColouring, telescope, gapsOf, legalGap, legalRange]

theorem feasible_iff (n : Nat) (blue : Nat → Nat → Prop) :
    (∃ gap, intervalEquations n blue gap) ↔ (∃ h, twoPathColouring n blue h) := by
  constructor
  · rintro ⟨gap, witness⟩
    refine ⟨colorsOf gap, (equationsOfGaps n blue (colorsOf gap)).mp ?_⟩
    rw [recoveredGaps]
    exact witness
  · rintro ⟨h, witness⟩
    exact ⟨gapsOf h, (equationsOfGaps n blue h).mpr witness⟩

end PermutationRangeTension
