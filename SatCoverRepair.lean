import Std

/-! Local and path invariants for rewiring a signed literal in a lifted CNF. -/
namespace SatCoverRepair

def bad (truth : Bool) : Nat := if truth then 0 else 1

theorem complementary_clauses (a b c : Bool) :
    bad (a || b || c) + bad (!a || !b || !c) =
      (if a = b ∧ b = c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

/-- The changed occurrence has the same polarity at its two ends.
The other literals in each clause can have arbitrary disjunctions. -/
theorem one_switch (otherLeft otherRight left right : Bool) :
    bad (otherLeft || left) + bad (otherRight || right) ≤
      bad (otherLeft || right) + bad (otherRight || left) + 1 := by
  cases otherLeft <;> cases otherRight <;> cases left <;> cases right <;> decide

/-- The initial defect of one fixed assignment gives a bound on every path. -/
theorem path_bound (defects : Nat → Nat) (r : Nat)
    (step : ∀ i, i < r → defects i ≤ defects (i + 1) + 1) :
    defects 0 ≤ defects r + r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have earlier := ih (fun i hi => step i (Nat.lt_succ_of_lt hi))
    have lastStep := step r (Nat.lt_succ_self r)
    omega

/-- Whole clauses on three distinct sheets. The donor is initially all true.
Two independent switches can use different donor ports. -/
theorem two_independent_donations (first second : Bool) :
    bad ((!first) || (!second) || true) + bad first + bad second =
      2 - (first.toNat + second.toNat) := by
  cases first <;> cases second <;> decide

theorem one_donation (useSwitch : Bool) :
    bad ((!useSwitch) || true || true) + bad useSwitch =
      1 - useSwitch.toNat := by
  cases useSwitch <;> decide

/-- Any number of sheets at least two partitions into pairs and at most one triple. -/
theorem sheet_blocks (d : Nat) (hd : 2 ≤ d) :
    ∃ p t : Nat, t ≤ 1 ∧ 2 * p + 3 * t = d := by
  by_cases even : d % 2 = 0
  · exact ⟨d / 2, 0, by omega, by omega⟩
  · exact ⟨(d - 3) / 2, 1, by omega, by omega⟩

#print axioms complementary_clauses
#print axioms one_switch
#print axioms path_bound
#print axioms two_independent_donations
#print axioms one_donation
#print axioms sheet_blocks

end SatCoverRepair
