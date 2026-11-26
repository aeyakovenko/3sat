import Std

/-! Evaluating the signed support expansion for repeated word reads.
After agreement on repeated addresses and on visible bits has been checked,
each private row occurs at most once. Its two values below are the actual
and claimed private words. A code only contributes when all of its selected
labels match the table. -/
namespace RepeatedReadChannels

abbrev Entry := Nat × Nat

/-- Sum the surviving channels, distinguishing the skip and the negative
select channel at a request for a zero private word. -/
def channelSum : List Entry → Int
  | [] => 1
  | (actual, claimed) :: rest =>
    let tail := channelSum rest
    if claimed = 0 then
      tail - (if actual = 0 then 0 else tail)
    else
      if actual = claimed then tail else 0

def agreement : List Entry → Int
  | [] => 1
  | (actual, claimed) :: rest =>
    if actual = claimed then agreement rest else 0

theorem channelSum_eq (xs : List Entry) : channelSum xs = agreement xs := by
  induction xs with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨actual, claimed⟩ := row
    by_cases c : claimed = 0
    · subst claimed
      by_cases a : actual = 0 <;> simp [channelSum, agreement, ih, a]
    · by_cases same : actual = claimed <;> simp [channelSum, agreement, ih, c, same]

/-- Counts all labeled supports of permitted size by choosing whether to
skip the next row or select one of its nonzero labels. -/
def supportCount : List Nat → Nat → Nat
  | [], _ => 1
  | _ :: _, 0 => 1
  | choices :: rest, budget + 1 =>
    supportCount rest (budget + 1) + choices * supportCount rest budget

def fullCount : List Nat → Nat
  | [] => 1
  | c :: rest => (1 + c) * fullCount rest

theorem supportCount_saturated (choices : List Nat) (t : Nat) (h : choices.length ≤ t) :
    supportCount choices t = fullCount choices := by
  induction choices generalizing t with
  | nil => simp [supportCount, fullCount]
  | cons c rest ih =>
    cases t with
    | zero => simp at h
    | succ t =>
      have len : rest.length ≤ t := Nat.le_of_succ_le_succ h
      simp [supportCount, fullCount, ih t len, ih (t+1) (by omega), Nat.add_mul]

end RepeatedReadChannels
