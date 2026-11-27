import Std

namespace ExecutedOperandBound

/-- In an unselected instruction each of the two accounting slots is either
    occupied by a marked load's direct use or available as a hole. Absent
    operands occupy unmarked slots. -/
def usesAt (slots : Bool × Bool) : Nat := slots.1.toNat + slots.2.toNat

def holesAt (slots : Bool × Bool) : Nat := 2 - usesAt slots

theorem slot_count (steps : List (Bool × Bool)) :
    (steps.map usesAt).sum + (steps.map holesAt).sum = 2 * steps.length := by
  induction steps with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨x, y⟩ := head
    cases x <;> cases y <;> simp [usesAt, holesAt] at * <;> omega

/-- All hypotheses here concern a single finite executed trace. The
    machine-specific perturbation and charge injections are supplied by the
    manuscript. The physical slot partition does not use a fractional step. -/
structure Charges (m T D a b e r d s j J : Nat) : Prop where
  markedSteps : m ≤ T
  /-- One direct use per marked token, plus its excess uses. -/
  directUses : D = m + a
  /-- The nonselected instructions have two accounting slots apiece. -/
  slotPartition : D + b = 2 * (T - m)
  excess : e = a + b
  /-- Repeatedly used tokens and other original loads cover the dirty cells. -/
  dirty : d ≤ a + r
  /-- Dirty cells, clean cells paired with dirty uses, underfull instructions,
      and the clean pairs that are stores, ALUs or exceptional addresses. -/
  cover : m ≤ d + (d + a) + b + 2 * (s + j + J)
  /-- Extra original loads and store witnesses charge different dummy slots;
      nonexceptional ALU witnesses charge actual, unmarked operands. -/
  distinctHoles : r + s + j ≤ b

theorem clean_pair_charge (h : Charges m T D a b e r d s j J) :
    m ≤ 3 * e + 2 * J := by
  obtain ⟨_, _, _, he, hd, hc, hh⟩ := h
  omega

theorem total_step_charge (h : Charges m T D a b e r d s j J) :
    5 * m ≤ 3 * T + J := by
  have bound := clean_pair_charge h
  obtain ⟨hm, hD, hp, he, _, _, _⟩ := h
  omega

/-- The baseline and strengthened bounds are both rounded up, including
    when the exceptional-address allowance exceeds five times m. -/
theorem rounded_lower_bounds (h : Charges m T D a b e r d s j J) :
    (3 * m + 1) / 2 ≤ T ∧ ((5 * m - J) + 2) / 3 ≤ T ∧
    ((m - 2 * J) + 2) / 3 ≤ e := by
  have times := total_step_charge h
  have extra := clean_pair_charge h
  obtain ⟨hm, hD, hp, _, _, _, _⟩ := h
  omega

/-- Even with no exceptional ALUs the numerical hypotheses allow equality
    at every multiple of three marked words. -/
theorem triple_counts (k : Nat) :
    Charges (3*k) (5*k) (3*k) 0 k k 0 0 0 k 0 := by
  constructor <;> omega

end ExecutedOperandBound
