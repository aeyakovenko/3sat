import Std

namespace FiveHalvesLift

/-- Program-explicit form of the journal's `five_halves` inequality
    (lean/FirstGeneratedNativeAddresses.lean: 5m <= 2T + sparse + 2 init),
    with the D1 trace:  sparse <= 2z + 5 sOut + c0  (z = file-only exceptional
    address values, sOut = preavailable values outside the marked interval),
    init <= sIn, and sIn + sOut <= 2C + d0 (at most two literals per stored
    instruction, d0 machine/layout values). -/
theorem traced (m T sparse init z sIn sOut c0 C d0 : Nat)
    (five : 5*m ≤ 2*T + sparse + 2*init)
    (hs : sparse ≤ 2*z + 5*sOut + c0) (hi : init ≤ sIn)
    (stock : sIn + sOut ≤ 2*C + d0) :
    5*m ≤ 2*T + 2*z + 10*C + 5*d0 + c0 := by omega

/-- Deadline K = 2 (4 steps per two words of the ceiling n/w <= m + b0).
    If z <= m/4 and m > 20C + 2e0 + 8b0 then no run meets 2(m+b0). -/
theorem fails_at_two (m T z C e0 b0 : Nat)
    (lower : 5*m ≤ 2*T + 2*z + 10*C + e0)
    (deadline : T ≤ 2*(m + b0))
    (absorb : 4*z ≤ m) (big : m > 20*C + 2*e0 + 8*b0) : False := by omega

/-- Deadline K = 9/4.  If z <= m/8 and m > 40C + 4e0 + 18b0 then no run meets
    (9/4)(m+b0). -/
theorem fails_at_nine_quarters (m T z C e0 b0 : Nat)
    (lower : 5*m ≤ 2*T + 2*z + 10*C + e0)
    (deadline : 4*T ≤ 9*(m + b0))
    (absorb : 8*z ≤ m) (big : m > 40*C + 4*e0 + 18*b0) : False := by omega

/-- Successor at K = 9/4: the size condition for C transfers to C+1 after
    adding 40 marked words (the absorption condition is a property of m alone
    and is assumed at the new m). -/
theorem successor_nine_quarters (m C e0 b0 : Nat)
    (big : m > 40*C + 4*e0 + 18*b0) :
    m + 40 > 40*(C+1) + 4*e0 + 18*b0 := by omega

/-- Successor at K = 2: add 20 marked words per extra instruction. -/
theorem successor_two (m C e0 b0 : Nat)
    (big : m > 20*C + 2*e0 + 8*b0) :
    m + 20 > 20*(C+1) + 2*e0 + 8*b0 := by omega

/-- Sharpness of the K = 9/4 hypothesis for this arithmetic: with a weaker size
    bound the contradiction is not derivable (witness values). -/
example : ¬ (∀ (m T z C e0 b0 : Nat), 5*m ≤ 2*T + 2*z + 10*C + e0 →
    4*T ≤ 9*(m + b0) → 8*z ≤ m → m > 39*C + 4*e0 + 18*b0 → False) := by
  intro h
  exact h 40 90 5 1 0 0 (by decide) (by decide) (by decide) (by decide)

end FiveHalvesLift
