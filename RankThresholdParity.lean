import Std

namespace RankThresholdParity

/-- Gaussian binomial coefficients at q = 2, via the q-Pascal recurrence. -/
def gaussian : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | s + 1, k + 1 => 2^(k+1) * gaussian s (k+1) + gaussian s k

theorem gaussian_parity (s k : Nat) : gaussian s k % 2 = if k ≤ s then 1 else 0 := by
  induction s generalizing k with
  | zero => cases k <;> simp [gaussian]
  | succ s ih =>
    cases k with
    | zero => simp [gaussian]
    | succ k =>
      have even : (2^(k+1) * gaussian s (k+1)) % 2 = 0 := by
        rw [Nat.pow_succ, Nat.mul_right_comm]
        simp
      rw [gaussian, Nat.add_mod, even, Nat.zero_add, Nat.mod_mod, ih]
      simp

/-- Ordered change-of-basis group orders, |GL(j+1,2)|=(2^(j+1)-1)2^j|GL(j,2)|. -/
def glOrder : Nat → Nat
  | 0 => 1
  | j+1 => 2^j * ((2^(j+1)-1) * glOrder j)

def rankCount (m j : Nat) : Nat := gaussian m j * gaussian m j * glOrder j

theorem rankCount_zero (m : Nat) : rankCount m 0 = 1 := by
  cases m <;> simp [rankCount, gaussian, glOrder]

theorem rankCount_one (m : Nat) (hm : 0 < m) : rankCount m 1 % 2 = 1 := by
  have hg := gaussian_parity m 1
  have h : 1 ≤ m := hm
  simp [h] at hg
  simp [rankCount, glOrder, Nat.mul_mod, hg]

theorem rankCount_high (m j : Nat) : rankCount m (j+2) % 2 = 0 := by
  have even : 2^(j+1) % 2 = 0 := by rw [Nat.pow_succ]; simp
  have hg : glOrder (j+2) % 2 = 0 := by
    change (2^(j+1) * _) % 2 = 0
    rw [Nat.mul_mod, even]
    simp
  change (_ * glOrder (j+2)) % 2 = 0
  rw [Nat.mul_mod, hg]
  simp

/-- Only the additive laws of a characteristic-two coefficient field are used. -/
structure Coeff (F : Type) where
  zero : F
  plus : F → F → F
  leftZero : ∀ x, plus zero x = x
  commute : ∀ x y, plus x y = plus y x
  assoc : ∀ x y z, plus (plus x y) z = plus x (plus y z)
  double : ∀ x, plus x x = zero

namespace Coeff

variable {F : Type} (g : Coeff F)

theorem rightZero (x : F) : g.plus x g.zero = x := by rw [g.commute, g.leftZero]

theorem cancelRight (x y : F) : g.plus (g.plus x y) y = x := by
  rw [g.assoc, g.double, g.rightZero]

theorem unequalSum {x y : F} (diff : x ≠ y) : g.plus x y ≠ g.zero := by
  intro eq
  apply diff
  calc
    x = g.plus (g.plus x y) y := (g.cancelRight x y).symm
    _ = y := by rw [eq, g.leftZero]

def times : Nat → F → F
  | 0, _ => g.zero
  | n+1, x => g.plus (times n x) x

theorem times_parity (n : Nat) (x : F) :
    g.times n x = if n % 2 = 0 then g.zero else x := by
  induction n with
  | zero => simp [times]
  | succ n ih =>
    rw [times, ih]
    by_cases even : n % 2 = 0
    · have odd : (n+1) % 2 ≠ 0 := by omega
      simp [even, odd, g.leftZero]
    · have next : (n+1) % 2 = 0 := by omega
      simp [even, next, g.double]

/-- The subspace-transcript sum with kernel dimension d-r and query dimension
d-j acts as the rank threshold, assuming the Gaussian subspace count. -/
theorem kernel_threshold (d r j : Nat) (hr : r ≤ d) (hj : j ≤ d) (x : F) :
    g.times (gaussian (d-r) (d-j)) x = if r ≤ j then x else g.zero := by
  rw [g.times_parity, gaussian_parity]
  by_cases small : r ≤ j
  · have sub : d-j ≤ d-r := by omega
    simp [small, sub]
  · have sub : ¬ d-j ≤ d-r := by omega
    simp [small, sub]

/-- Counts integrated against the shifted rank function through the first ℓ ranks. -/
def rankIntegral (f : Nat → F) (h m : Nat) : Nat → F
  | 0 => g.zero
  | l+1 => g.plus (rankIntegral f h m l) (g.times (rankCount m l) (f (h+l)))

theorem integral_from_rank_counts (f : Nat → F) (h m n : Nat) (hm : 0 < m) :
    g.rankIntegral f h m (n+2) = g.plus (f h) (f (h+1)) := by
  induction n with
  | zero =>
    simp [rankIntegral, times_parity, rankCount_zero, rankCount_one m hm, g.leftZero]
  | succ n ih =>
    change g.plus (g.rankIntegral f h m (n+2)) _ = _
    rw [ih, g.times_parity, rankCount_high]
    simp [g.rightZero]

/-- One adaptive transcript leaf on the block. Its two direction ranks are
fixed at the leaf; consistency may be false. Linear independence and
counting matrix completions are the manuscript input to this formula. -/
structure Fiber (F : Type) where
  leftRank : Nat
  rightRank : Nat
  consistent : Bool
  coefficient : F

def fiberMass (m : Nat) (p : Fiber F) : F :=
  if p.consistent then
    g.times (2^((m-p.leftRank)*(m-p.rightRank))) p.coefficient
  else g.zero

theorem short_fiber (m : Nat) (p : Fiber F) (short : p.leftRank + p.rightRank < m) :
    g.fiberMass m p = g.zero := by
  have e : 0 < (m-p.leftRank)*(m-p.rightRank) := Nat.mul_pos (by omega) (by omega)
  obtain ⟨j, hj⟩ : ∃ j, (m-p.leftRank)*(m-p.rightRank) = j+1 :=
    ⟨(m-p.leftRank)*(m-p.rightRank)-1, by omega⟩
  have even : 2^((m-p.leftRank)*(m-p.rightRank)) % 2 = 0 := by
    rw [hj, Nat.pow_succ]; simp
  simp [fiberMass, g.times_parity, even]

def representationMass (m : Nat) : List (Fiber F) → F
  | [] => g.zero
  | p :: ps => g.plus (g.fiberMass m p) (representationMass m ps)

theorem short_representation (m : Nat) (ps : List (Fiber F))
    (short : ∀ p ∈ ps, p.leftRank + p.rightRank < m) :
    g.representationMass m ps = g.zero := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [representationMass, g.short_fiber m p (short p (by simp)), g.leftZero]
    exact ih (by intro q hq; exact short q (by simp [hq]))

/-- Once the geometric counting identities are supplied, equality of the two
integrals forces a transcript of total direction rank at least m=d-h. -/
theorem rank_change_requires_cost (f : Nat → F) (h m cost : Nat) (hm : 0 < m)
    (changeAt : f h ≠ f (h+1)) (ps : List (Fiber F))
    (budget : ∀ p ∈ ps, p.leftRank + p.rightRank ≤ cost)
    (represents : g.representationMass m ps = g.rankIntegral f h m (m+1)) :
    m ≤ cost := by
  by_cases small : m ≤ cost
  · exact small
  exfalso
  have hc : cost < m := by omega
  have allShort := g.short_representation m ps (by
    intro p hp
    exact Nat.lt_of_le_of_lt (budget p hp) hc)
  obtain ⟨n, rfl⟩ : ∃ n, m = n+1 := ⟨m-1, by omega⟩
  rw [allShort, g.integral_from_rank_counts f h (n+1) n hm] at represents
  exact g.unequalSum changeAt represents.symm

/-- Start with f(start+span) and add the scaled threshold indicators in
descending order; in characteristic two the adjacent difference is their sum. -/
def expansion (f : Nat → F) (rank start : Nat) : Nat → F
  | 0 => f start
  | n+1 =>
    g.plus (if rank ≤ start then g.plus (f start) (f (start+1)) else g.zero)
      (expansion f rank (start+1) n)

theorem threshold_expansion (f : Nat → F) (r h n : Nat) (inRange : r ≤ h+n) :
    g.expansion f r h n = if r ≤ h then f h else f r := by
  induction n generalizing h with
  | zero =>
    have h' : r ≤ h := by omega
    simp [expansion, h']
  | succ n ih =>
    rw [expansion, ih (h+1) (by omega)]
    by_cases early : r ≤ h
    · have next : r ≤ h+1 := by omega
      simp [early, next, g.cancelRight]
    · simp only [early, ↓reduceIte, g.leftZero]
      by_cases next : r ≤ h+1
      · have eq : r = h+1 := by omega
        simp [eq]
      · simp [next]

theorem flat_prefix_expansion (f : Nat → F) (r h n : Nat) (inRange : r ≤ h+n)
    (flat : ∀ i, i ≤ h → f i = f h) : g.expansion f r h n = f r := by
  rw [g.threshold_expansion f r h n inRange]
  by_cases small : r ≤ h
  · simp [small, flat r small]
  · simp [small]

/-- The absence of an earlier adjacent change supplies exactly the flat-prefix
hypothesis needed to start the threshold sum at h rather than zero. -/
theorem first_change_expansion (f : Nat → F) (d r h : Nat) (hr : r ≤ d) (hh : h ≤ d)
    (noEarlier : ∀ j, j < h → f j = f (j+1)) :
    g.expansion f r h (d-h) = f r := by
  have constant : ∀ j, j ≤ h → f j = f 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro bound
      rw [← noEarlier j (by omega)]
      exact ih (by omega)
  apply g.flat_prefix_expansion f r h (d-h) (by omega)
  intro i hi
  exact (constant i hi).trans (constant h (Nat.le_refl h)).symm

end Coeff
end RankThresholdParity
