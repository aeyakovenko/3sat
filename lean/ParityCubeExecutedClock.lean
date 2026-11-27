import Std

namespace ParityCubeExecutedClock

/-- r distinct selected original LOADs, each having a directly consumed
    definition. Only other instructions can consume those definitions. -/
theorem exposure_clock {r T uses : Nat} (loads : r ≤ T)
    (exposed : r ≤ uses) (slots : uses ≤ 2*(T-r)) :
    r+(r+1)/2 ≤ T := by omega

/-- Each of r-d-s indirect addresses that was absent initially needs its
    own native numerical result or literal STORE. Both count as nonbranch. -/
theorem address_clock {r d s producers U : Nat}
    (coverage : r ≤ d+s+producers) (events : r+producers ≤ U) :
    2*r ≤ U+d+s := by omega

theorem direct_sites_at_pair_clock {r d s U T : Nat}
    (h : 2*r ≤ U+d+s) (u : U ≤ T) (t : T ≤ r+(r+1)/2) :
    r/2 ≤ d+s := by omega

/-- Grouping equal ordered raw-word pairs lets one native equality branch
    compute parity of two independent coordinates. -/
theorem pair_test {α : Type} [DecidableEq α] (lo hi : α) (hne : lo ≠ hi)
    (a b : Bool) : decide ((if a then hi else lo) ≠ (if b then hi else lo))
      = Bool.xor a b := by
  cases a <;> cases b <;> simp [hne, Ne.symm hne]

/-- Two LOADs and one branch per pair, one LOAD and one branch per singleton. -/
theorem grouped_clock (pairs singles : Nat) :
    2*(3*pairs+2*singles) = 3*(2*pairs+singles)+singles := by omega

end ParityCubeExecutedClock
