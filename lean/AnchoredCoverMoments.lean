import Std

namespace AnchoredCoverMoments

/-- One entry is the hit count on one equally weighted outcome. Listing an
    outcome repeatedly implements any rational distribution. -/
def total (f : Int → Int) (xs : List Nat) : Int := (xs.map (fun (a : Nat) => f a)).sum

def hits (xs : List Nat) : Int := total id xs
def squares (xs : List Nat) : Int := total (fun x => x*x) xs
def pairs (xs : List Nat) : Int := total (fun x => x*(x-1)) xs
def misses (xs : List Nat) : Int := xs.count 0
def size (xs : List Nat) : Int := xs.length

private theorem squareNonnegative (x : Int) : 0 ≤ x*x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem missContribution (xs : List Nat) (k c : Int) :
    misses xs*(c*c) ≤ total (fun x => (k*x-c)*(k*x-c)) xs := by
  induction xs with
  | nil => simp [misses, total]
  | cons a xs ih =>
    cases a with
    | zero =>
      simpa [misses, total, Int.add_mul, Int.add_comm, Int.neg_mul_neg] using
        (Int.add_le_add_right ih (c*c))
    | succ a =>
      have h := squareNonnegative (k * ((a+1 : Nat) : Int) - c)
      simp [misses, total] at *
      omega

private theorem expansion (xs : List Nat) (k c : Int) :
    total (fun x => (k*x-c)*(k*x-c)) xs + ((k*c)*hits xs + (k*c)*hits xs) =
      (k*k)*squares xs + size xs*(c*c) := by
  induction xs with
  | nil => simp [hits, squares, total, size]
  | cons a xs ih =>
    simp only [hits, squares, total, size, List.map_cons, List.sum_cons,
      List.length_cons, Int.natCast_add, Int.cast_ofNat_Int, Int.add_mul, Int.mul_add,
      Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one, id_eq,
      Int.mul_left_comm, Int.mul_comm, Int.mul_assoc]
      at ih ⊢
    omega

/-- The denominator-cleared zero-hit bound around an arbitrary center c/k. -/
theorem scaledBound (xs : List Nat) (k c : Int) :
    misses xs*(c*c) + ((k*c)*hits xs + (k*c)*hits xs) ≤ (k*k)*squares xs + size xs*(c*c) := by
  rw [← expansion]
  exact Int.add_le_add_right (missContribution xs k c) _

/-- Z S² ≤ N (N Q − S²), where S/N and Q/N are the two raw moments.
    This is the integer form of Pr[X=0] E[X]² ≤ Var(X). -/
theorem zeroVariance (xs : List Nat) :
    misses xs*(hits xs*hits xs) ≤
      size xs*(size xs*squares xs - hits xs*hits xs) := by
  have h := scaledBound xs (size xs) (hits xs)
  simp only [Int.mul_sub, Int.mul_left_comm, Int.mul_comm, Int.mul_assoc] at h ⊢
  omega

/-- At each outcome x² = x + x(x−1); the second term counts ordered pairs
    of distinct hits. -/
theorem squareIdentity (xs : List Nat) : squares xs = hits xs + pairs xs := by
  induction xs with
  | nil => simp [squares, hits, pairs, total]
  | cons a xs ih =>
    simp [squares, hits, pairs, total, Int.mul_sub] at *
    omega

theorem zeroVarianceFromPairs (xs : List Nat) :
    misses xs*(hits xs*hits xs) ≤
      size xs*(size xs*(hits xs+pairs xs) - hits xs*hits xs) := by
  rw [← squareIdentity]
  exact zeroVariance xs

private theorem nonnegativeMoments (xs : List Nat) : 0 ≤ hits xs ∧ 0 ≤ pairs xs := by
  induction xs with
  | nil => simp [hits, pairs, total]
  | cons a xs ih =>
    cases a with
    | zero => simpa [hits, pairs, total] using ih
    | succ a =>
      have h : 0 ≤ ((a : Int)+1)*a := Int.mul_nonneg (by omega) (by omega)
      simp [hits, pairs, total] at *
      omega

/-- The sharper zero bound obtained by optimizing the center: Z Q + S² ≤ N Q. -/
theorem zeroSecondMoment (xs : List Nat) :
    misses xs*squares xs + hits xs*hits xs ≤ size xs*squares xs := by
  by_cases pos : 0 < squares xs
  · have h := scaledBound xs (hits xs) (squares xs)
    have scaled : squares xs * (misses xs*squares xs + hits xs*hits xs) ≤
        squares xs * (size xs*squares xs) := by
      simp only [Int.mul_add, Int.mul_left_comm, Int.mul_comm, Int.mul_assoc] at h ⊢
      omega
    exact Int.le_of_mul_le_mul_left scaled pos
  · have hn := nonnegativeMoments xs
    have hi := squareIdentity xs
    have empty : squares xs = 0 := by omega
    have noHits : hits xs = 0 := by omega
    simp [empty, noHits]

/-- First-moment lower bounds and first-plus-ordered-pair upper bounds may
    be substituted directly, including those from approximately biased hits. -/
theorem coverBudget (xs : List Nat) (lo hi : Int) (nonnegative : 0 ≤ lo)
    (first : lo ≤ hits xs) (second : hits xs + pairs xs ≤ hi) :
    lo*lo ≤ (size xs - misses xs)*hi := by
  have count : xs.count 0 ≤ xs.length := List.count_le_length
  have occupied : 0 ≤ size xs - misses xs := by
    unfold size misses
    omega
  have exactBound := zeroSecondMoment xs
  have upper : squares xs ≤ hi := by rwa [squareIdentity]
  calc
    _ ≤ hits xs*lo := Int.mul_le_mul_of_nonneg_right first nonnegative
    _ ≤ hits xs*hits xs := Int.mul_le_mul_of_nonneg_left first (by omega)
    _ ≤ (size xs-misses xs)*squares xs := by rw [Int.sub_mul]; omega
    _ ≤ _ := Int.mul_le_mul_of_nonneg_left upper occupied

end AnchoredCoverMoments
