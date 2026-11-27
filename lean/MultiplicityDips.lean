import Std

namespace MultiplicityDips

/-- The most recent entry of each history comes first. -/
def pending (threshold : Nat) : List Nat → Nat
  | [] => 0
  | b :: hist => if b < threshold then 0 else pending threshold hist + 1

def charge (threshold b : Nat) (hist : List Nat) : Nat :=
  if b < threshold then pending threshold hist + 1 else 0

def paid (threshold : Nat) : List Nat → Nat
  | [] => 0
  | b :: hist => paid threshold hist + charge threshold b hist

theorem conservation (t : Nat) (hist : List Nat) :
    paid t hist + pending t hist = hist.length := by
  induction hist with
  | nil => rfl
  | cons b hist ih =>
    by_cases hb : b < t <;> simp [paid, pending, charge, hb] at * <;> omega

theorem highWindow (t : Nat) (window older : List Nat)
    (high : ∀ x ∈ window, t ≤ x) :
    window.length ≤ pending t (window ++ older) := by
  induction window with
  | nil => simp
  | cons x rest ih =>
    have hx : ¬x < t := by have := high x (by simp); omega
    have hrest := ih (fun y hy => high y (by simp [hy]))
    simp [pending,hx]
    omega

/-- The thresholds b+1 through b+levels singled out by a multiplicity dip. -/
def levelsPaid (b : Nat) (hist : List Nat) : Nat → Nat
  | 0 => 0
  | levels + 1 => levelsPaid b hist levels + charge (b + levels + 1) b hist

theorem windowPayment (b levels : Nat) (window older : List Nat)
    (high : ∀ x ∈ window, b + levels ≤ x) :
    (window.length+1)*levels ≤ levelsPaid b (window ++ older) levels := by
  induction levels with
  | zero => simp [levelsPaid]
  | succ levels ih =>
    have prior := ih (fun x hx => by have := high x hx; omega)
    have last := highWindow (b+levels+1) window older high
    simp only [levelsPaid, charge, show b < b+levels+1 by omega, if_true,
      Nat.mul_succ]
    omega

/-- Past block minima, most recent first. -/
def clearance : List Nat → Nat
  | [] => 1
  | m :: older => min (clearance older) m + 1

theorem qualifiesBelowClearance (i : Nat) (older : List Nat)
    (start : i ≤ older.length)
    (past : ∀ j (hj : j < older.length), i < older[j] + j + 1) :
    i < clearance older := by
  induction older generalizing i with
  | nil => simp [clearance] at *; omega
  | cons m older ih =>
    cases i with
    | zero => simp [clearance]
    | succ k =>
      have hs : k ≤ older.length := by simpa using start
      have hp : ∀ j (hj : j < older.length), k < older[j] + j + 1 := by
        intro j hj
        have hl := past (j+1) (by simpa using hj)
        simp only [List.getElem_cons_succ] at hl
        omega
      have hprev := ih k hs hp
      have hm := past 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at hm
      simp only [clearance, Nat.succ_lt_succ_iff, Nat.lt_min]
      omega

theorem decreasingCount (xs : List Nat) (lo hi : Nat)
    (decreasing : xs.Pairwise (· > ·)) (low : ∀ x ∈ xs, lo ≤ x)
    (high : ∀ x ∈ xs, x < hi) : xs.length ≤ hi-lo := by
  induction xs generalizing hi with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨before, tail⟩ := List.pairwise_cons.mp decreasing
    have hcount := ih x tail (fun y hy => low y (by simp [hy])) before
    have hlow := low x (by simp)
    have hhigh := high x (by simp)
    simp only [List.length_cons]
    omega

def capacity : List Nat → Nat
  | [] => 0
  | m :: older => capacity older + (clearance older - m)

theorem blockBudget (minima : List Nat) :
    capacity minima + clearance minima = minima.length + 1 := by
  induction minima with
  | nil => rfl
  | cons m older ih =>
    simp only [capacity,clearance,List.length_cons]
    omega

end MultiplicityDips
