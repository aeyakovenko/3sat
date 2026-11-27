import Std

namespace ExceptionalBands

/-- Ignore common denominators and count entries outside the two integer
    endpoints of a band. -/
def lowCount (lower : Nat) (xs : List Nat) := (xs.filter (· ≤ lower)).length
def bandCount (lower upper : Nat) (xs : List Nat) :=
  (xs.filter (fun x => decide (lower < x ∧ x ≤ upper))).length
def highCount (upper : Nat) (xs : List Nat) := (xs.filter (upper < ·)).length

theorem band_partition (xs : List Nat) {lower upper : Nat} (good : lower ≤ upper) :
    lowCount lower xs + bandCount lower upper xs + highCount upper xs = xs.length := by
  induction xs with
  | nil => simp [lowCount,bandCount,highCount]
  | cons x xs ih =>
    by_cases low : x ≤ lower
    · have top : x ≤ upper := Nat.le_trans low good
      simp [lowCount, bandCount, highCount, low, Nat.not_lt_of_ge low,
        Nat.not_lt_of_ge top] at *
      omega
    · have pos := Nat.lt_of_not_ge low
      by_cases inside : x ≤ upper
      · simp [lowCount, bandCount, highCount, low, pos, inside,
          Nat.not_lt_of_ge inside] at *
        omega
      · have big := Nat.lt_of_not_ge inside
        simp [lowCount, bandCount, highCount, low, pos, inside, big] at *
        omega

theorem expensive_entries (xs : List Nat) (upper : Nat) :
    (upper + 1) * highCount upper xs ≤ xs.sum := by
  induction xs with
  | nil => simp [highCount]
  | cons x xs ih =>
    by_cases h : upper < x
    · simpa [highCount, h, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using Nat.add_le_add (Nat.succ_le_of_lt h) ih
    · simp [highCount, h] at *
      omega

theorem outside_bound (xs : List Nat) {lower upper finiteExceptions total : Nat}
    (order : lower ≤ upper) (fewSmall : lowCount lower xs ≤ finiteExceptions)
    (mass : xs.sum ≤ total) :
    xs.length ≤ bandCount lower upper xs + finiteExceptions + total / (upper+1) := by
  have budget := Nat.le_trans (expensive_entries xs upper) mass
  have high : highCount upper xs ≤ total / (upper+1) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    rwa [Nat.mul_comm]
  have split := band_partition xs order
  omega

/-- The saved bits absorb the self-delimiting parameter and fixed tag.
    The +1 admits the last possible offset in the length prefix. -/
theorem selected_rank_is_short {j k rCode d dCode tag m : Nat}
    (precision : k = rCode+d) (rankFits : k ≤ j) (room : j ≤ m)
    (margin : tag + dCode + 1 < d) :
    tag + rCode + dCode + (j-k+1) + (m-j) < m := by omega

/-- Reusing a scale description for every rank in a long audit. -/
theorem audit_rank_is_short {b j m header scaleCode rankBits saving : Nat}
    (bits : rankBits + saving = 2*b) (fits : 2*b ≤ j) (room : j ≤ m)
    (margin : header + scaleCode + 1 < saving) :
    header + scaleCode + rankBits + (j-2*b+1) + (m-j) < m := by omega

private theorem sumLast (xs : List Nat) (x : Nat) :
    (xs ++ [x]).sum = xs.sum + x := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih, Nat.add_assoc]

/-- Finite geometric sum bounding the repeated audit charge of one block
    after scaling the smallest unit to one. -/
theorem dyadic_tail (k : Nat) :
    ((List.range k).map (fun i => 2^i)).sum + 1 = 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      sumLast, Nat.pow_succ]
    omega

end ExceptionalBands
