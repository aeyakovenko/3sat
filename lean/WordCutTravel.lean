import Std

namespace WordCutTravel

/-- Cut c separates the word addresses 0,...,c from the larger addresses. -/
def cross (c a b : Nat) : Nat :=
  if (a ≤ c ∧ c < b) ∨ (b ≤ c ∧ c < a) then 1 else 0

def firstCuts (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k+1 => firstCuts k f + f k

/-- Distance within the address range observed by the first n cuts. -/
def clipped (n a b : Nat) : Nat :=
  (min a n - min b n) + (min b n - min a n)

/-- The exact number of distinct integer cuts crossed by one word hop. -/
theorem one_hop (n a b : Nat) :
    firstCuts n (fun c => cross c a b) = clipped n a b := by
  induction n with
  | zero => simp [firstCuts, clipped]
  | succ k ih =>
    rw [firstCuts, ih]
    unfold clipped cross
    split <;> omega

private theorem sumPair (n : Nat) (f g : Nat → Nat) :
    firstCuts n (fun c => f c + g c) = firstCuts n f + firstCuts n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [firstCuts, ih]; omega

private theorem sumMono (n : Nat) {f g : Nat → Nat} (h : ∀ c, f c ≤ g c) :
    firstCuts n f ≤ firstCuts n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.add_le_add ih (h n)

private theorem sumConst (n k : Nat) : firstCuts n (fun _ => k) = n*k := by
  induction n with
  | zero => simp [firstCuts]
  | succ n ih => simp [firstCuts, ih, Nat.succ_mul]

/-- a is the first actual address and xs gives the remaining visits in time order. -/
def crossings (c a : Nat) : List Nat → Nat
  | [] => 0
  | b :: xs => cross c a b + crossings c b xs

def travel (n a : Nat) : List Nat → Nat
  | [] => 0
  | b :: xs => clipped n a b + travel n b xs

theorem cut_sum_eq_travel (n a : Nat) (xs : List Nat) :
    firstCuts n (fun c => crossings c a xs) = travel n a xs := by
  induction xs generalizing a with
  | nil => simp only [crossings, travel, sumConst, Nat.mul_zero]
  | cons b xs ih =>
    simp only [crossings, travel]
    rw [sumPair, one_hop, ih]

/-- Arbitrary selected cuts never charge a hop more than its clipped length. -/
theorem selected_cut_sum_le (includeCut : Nat → Bool) (n a : Nat) (xs : List Nat) :
    firstCuts n (fun c => if includeCut c then crossings c a xs else 0) ≤ travel n a xs := by
  rw [← cut_sum_eq_travel]
  apply sumMono
  intro c
  cases includeCut c <;> simp

def longHops (n h a : Nat) : List Nat → Nat
  | [] => 0
  | b :: xs =>
    (if h < clipped n a b then 1 else 0) + longHops n h b xs

theorem clipped_le_endpoint (n a b : Nat) : clipped n a b ≤ n := by
  unfold clipped
  omega

theorem clipped_le_actual (n a b : Nat) : clipped n a b ≤ (a-b)+(b-a) := by
  unfold clipped
  omega

/-- The excess over a per-hop allowance h is at most n per long hop.
    In particular any counted long hop also exceeds h in the real RAM address space. -/
theorem travel_le_allowance (n h a : Nat) (xs : List Nat) :
    travel n a xs ≤ xs.length * h + (longHops n h a xs) * n := by
  induction xs generalizing a with
  | nil => simp [travel, longHops]
  | cons b xs ih =>
    simp only [travel, longHops, List.length_cons, Nat.succ_mul, Nat.add_mul]
    have cap := clipped_le_endpoint n a b
    have rest := ih b
    split <;> simp only [Nat.one_mul, Nat.zero_mul] <;> omega

/-- A cut-crossing demand exceeding the short-hop budget and H full-range
    hops forces at least H+1 actual hops of clipped length greater than h. -/
theorem many_long_hops {n h a need H : Nat} {xs : List Nat}
    (includeCut : Nat → Bool)
    (demand : need ≤ firstCuts n (fun c => if includeCut c then crossings c a xs else 0))
    (excess : xs.length * h + H*n < need) :
    H < longHops n h a xs := by
  have lb := Nat.le_trans demand (selected_cut_sum_le includeCut n a xs)
  have ub := travel_le_allowance n h a xs
  apply Classical.byContradiction
  intro nope
  have le : longHops n h a xs ≤ H := by omega
  have mul := Nat.mul_le_mul_right n le
  omega

end WordCutTravel
