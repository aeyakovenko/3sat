import Std

namespace CyclicMatrixCentralizer

/-- The two top-to-socle nullities on three equal-dimensional vertices coincide. -/
theorem cyclicKernel (a b c : Nat) :
    a * c + b * a + c * b = a * b + b * c + c * a := by
  ac_rfl

/-- Rank-nullity for multiplication by u gives the pointwise bound in the square case. -/
theorem squareBound (c₀ c₁ c₂ a b c : Nat) (adjoint : c₂ = c₀)
    (kernelFits : a*b + b*c + c*a ≤ c₀)
    (imageFits : c₁ ≤ c₂ + (a*c + b*a + c*b)) : c₁ ≤ 2*c₀ := by
  rw [cyclicKernel, adjoint] at imageFits
  omega

/-- A residue class among m consecutive offsets occupies at most half when m ≥ 2. -/
theorem longChainOffsets (m : Nat) (hm : 2 ≤ m) : 2 * ((m+2)/3) ≤ m := by
  omega

/-- Both maps between a simple and a longer chain have grade one only in this case. -/
theorem exceptionalChain (i j t : Int) (forward : (j+t-1-i)%3 = 1)
    (backward : (i-j)%3 = 1) : t%3 = 0 ∧ (j-i)%3 = 2 := by
  omega

/-- After counting an orbit, the dimension-dependent exponent is nonpositive. -/
theorem orbitExponent (c₀ c₁ c₂ n s : Int) (adjoint : c₂ - c₀ = n-s)
    (centralizer : c₁ ≤ c₀ + c₂) :
    2*(s-n) + c₁ - 2*c₀ ≤ s-n := by
  omega

end CyclicMatrixCentralizer
