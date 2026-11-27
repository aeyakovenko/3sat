import Std

namespace DelayedExpertChoice

/-- The choice with smaller settled loss has final excess at most the
    remaining error budget minus the current margin, truncated at zero. -/
theorem prefixChoice (low high addedLow addedHigh budget : Nat)
    (leading : low ≤ high) (future : addedLow + addedHigh ≤ budget) :
    let chosen := low + addedLow
    let other := high + addedHigh
    chosen - min chosen other ≤ budget - (high - low) := by
  dsimp
  omega

/-- Pending starts are counted separately. The last future mistake must
    still satisfy the live threshold after earlier mistakes spent two names. -/
theorem unsettledCount (live threshold future pending : Nat)
    (last : 0 < future → threshold + 2*(future-1) ≤ live) :
    pending + future ≤ pending +
      (if threshold ≤ live then (live-threshold)/2+1 else 0) := by
  split
  · rename_i enough
    by_cases h : future = 0
    · omega
    · have bound := last (by omega); omega
  · rename_i few
    by_cases h : future = 0
    · omega
    · have bound := last (by omega); omega

/-- With two retirees per block, the public remaining live-rank bound at
    the checkpoint agrees exactly with the number of unobserved blocks. -/
theorem remainingCount (live threshold t : Nat)
    (ready : threshold ≤ live) (within : t < (live-threshold)/2+1) :
    threshold ≤ live-2*t ∧
      (live-2*t-threshold)/2+1 = ((live-threshold)/2+1)-t := by omega

/-- Following the prediction on all remaining blocks after a tied prefix
    realizes the entire remaining-block regret. -/
theorem tiedPrefixExcess (settled remaining : Nat) :
    settled + remaining - min (settled + remaining) settled = remaining := by omega

/-- The learner loses on every realized block. The two fixed experts split
    those losses according to the learner's successive choices. -/
theorem forcedOnlineRegret (first second : Nat) :
    (first+second+1)/2 ≤ (first+second) - min first second := by omega

/-- Alternating balances the count of choices exactly up to one. -/
theorem alternatingRegret (t : Nat) :
    t - min (t/2) ((t+1)/2) = (t+1)/2 := by omega

/-- On nonmatching histories, excess against a particular expert comes
    only from disagreements, with at most one unit lost per disagreement. -/
theorem disagreementBound (same chosenOnOther expertOnOther differences : Nat)
    (lossBound : chosenOnOther ≤ differences) :
    (same + chosenOnOther) - (same + expertOnOther) ≤ differences := by omega

end DelayedExpertChoice
