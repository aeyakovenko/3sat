import Std

namespace StaggeredRelease

/-- The metadata for the length and restricted residue is paid out of the
    repeated low-bit field, in addition to the forced leading zeroes. -/
theorem eligibleIsShort (m j overhead : Nat) (room : 2*j ≤ m)
    (metadata : overhead < j) :
    overhead + j + (m-2*j) < m := by omega

/-- If a literal is mandatory, all short names select their core before
    this shorter depth, regardless of which literal will be needed. -/
theorem coreDepth (m j body : Nat) (short : body + j < m) :
    body ≤ m-j-1 := by omega

/-- At depth m of one complete binary tree, even the longest valid core
    field occupies two complete sets of 2^j leaves. -/
theorem coreCell (m j : Nat) (fits : j < m) :
    2^(m-(m-j-1)) = 2*2^j := by
  have eq : m-(m-j-1) = j+1 := by omega
  rw [eq, Nat.pow_succ, Nat.mul_comm]

end StaggeredRelease
