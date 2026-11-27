import Std

namespace NearClockCoding

/-- The first grid boundary on or after a. -/
def gridIndex (a step : Nat) : Nat :=
  if a % step = 0 then a / step else a / step + 1

/-- An interval at least twice the cell width contains the selected
    aligned cylinder. Coordinates are in common integer grid units. -/
theorem alignedPlacement (a width step : Nat)
    (positive : 0 < step) (room : 2 * step ≤ width) :
    a ≤ gridIndex a step * step ∧ (gridIndex a step + 1) * step ≤ a + width := by
  have div := Nat.mod_add_div a step
  rw [Nat.mul_comm step (a / step)] at div
  have rem := Nat.mod_lt a positive
  by_cases exactGrid : a % step = 0
  · simp only [gridIndex, exactGrid, if_true, Nat.succ_mul]
    omega
  · simp only [gridIndex, exactGrid, if_false, Nat.succ_mul]
    omega

/-- Once the code cylinder is inside its requested interval it cannot
    overlap a disjoint earlier batch, even if that batch uses longer codes. -/
theorem earlierDisjoint (oldStart oldEnd cellStart cellEnd trueStart trueEnd : Nat)
    (inside : trueStart ≤ cellStart ∧ cellEnd ≤ trueEnd)
    (apart : oldEnd ≤ trueStart ∨ trueEnd ≤ oldStart) :
    oldEnd ≤ cellStart ∨ cellEnd ≤ oldStart := by omega

/-- Number of extra input bits read by a batch while its overlap and depth
    tests allow another read; start indexes an already cached prefix. -/
def readCount (need : Nat → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    if need start then 1 + readCount need (start+1) fuel else 0

/-- A check which has stopped at the true name depth cannot read past it
    from any cached prefix. This applies regardless of the check's fuel. -/
theorem noOverread (need : Nat → Bool) (target : Nat) (stops : need target = false)
    (start fuel : Nat) (ready : start ≤ target) :
    start + readCount need start fuel ≤ target := by
  induction fuel generalizing start with
  | zero => simpa [readCount] using ready
  | succ fuel ih =>
    by_cases more : need start = true
    · have lt : start < target := by
        by_cases eq : start = target
        · have : need start = false := eq ▸ stops
          simp [more] at this
        · omega
      have bound := ih (start+1) (by omega)
      simp only [readCount, more, if_true]
      omega
    · have done : need start = false := by cases v : need start <;> simp_all
      simpa [readCount, done] using ready

/-- The true matching batch reads all remaining bits whenever its
    ancestors still overlap and the input is long enough. -/
theorem exactConsumption (need : Nat → Bool) (target : Nat)
    (continues : ∀ j, j < target → need j = true) (stops : need target = false)
    (start fuel : Nat) (ready : start ≤ target) (enough : target ≤ start + fuel) :
    start + readCount need start fuel = target := by
  induction fuel generalizing start with
  | zero => simp only [readCount]; omega
  | succ fuel ih =>
    by_cases eq : start = target
    · subst start
      simp [readCount, stops]
    · have lt : start < target := by omega
      have bound := ih (start+1) (by omega) (by omega)
      simp only [readCount, continues _ lt, if_true]
      omega

/-- A skipped batch carries its cached input prefix into the next batch.
    Each batch carries its independently varying refinement budget. -/
def scan (start : Nat) : List ((Nat → Bool) × Nat) → Nat
  | [] => start
  | (need, fuel) :: rest => scan (start + readCount need start fuel) rest

/-- Disjointness at the target depth makes every preceding batch stop there
    or earlier, even across multiple changes of the search depth. -/
theorem scanBefore (earlier : List ((Nat → Bool) × Nat)) (start target : Nat)
    (cached : start ≤ target) (stops : ∀ b ∈ earlier, b.1 target = false) :
    scan start earlier ≤ target := by
  induction earlier generalizing start with
  | nil => exact cached
  | cons b rest ih =>
    rcases b with ⟨need, fuel⟩
    apply ih
    · exact noOverread need target (stops (need, fuel) (by simp)) start fuel cached
    · exact fun b hb => stops b (by simp [hb])

/-- The target batch reads exactly its name after an arbitrary safe scan. -/
theorem streamExact (earlier : List ((Nat → Bool) × Nat)) (target : Nat)
    (stops : ∀ b ∈ earlier, b.1 target = false) (matchNeed : Nat → Bool)
    (continues : ∀ j, j < target → matchNeed j = true)
    (finished : matchNeed target = false) :
    let cached := scan 0 earlier
    cached + readCount matchNeed cached target = target := by
  apply exactConsumption matchNeed target continues finished
  · exact scanBefore earlier 0 target (Nat.zero_le _) stops
  · omega

/-- Leaf descent needs only one comparison, including at a split boundary.
    This works after clearing the denominators of rational split endpoints. -/
theorem uniqueSide (a mid b x : Nat) (inside : a ≤ x ∧ x < b) :
    (a ≤ x ∧ x < mid ∧ ¬mid ≤ x) ∨ (mid ≤ x ∧ x < b ∧ ¬x < mid) := by
  omega

/-- A child's estimated share is at most num/den times its true share.
    Here exact and estimated counts use the same common denominator. -/
theorem shareUpper (child total estimate estimateTotal num den : Nat)
    (totalLower : total ≤ estimateTotal) (childUpper : estimate * den ≤ child * num) :
    (estimate * total) * den ≤ (child * estimateTotal) * num := by
  have step := Nat.mul_le_mul childUpper totalLower
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using step

/-- The denominator's approximation supplies the reverse share comparison. -/
theorem shareLower (child total estimate estimateTotal num den : Nat)
    (childLower : child ≤ estimate) (totalUpper : estimateTotal * den ≤ total * num) :
    (child * estimateTotal) * den ≤ (estimate * total) * num := by
  have step := Nat.mul_le_mul childLower totalUpper
  simpa [Nat.mul_assoc] using step

private def product : List Nat → Nat
  | [] => 1
  | x :: xs => x * product xs

/-- The product of n local comparisons in any common grid obeys the
    same multiplicative bound; numerators may vary independently. -/
theorem productPath (pairs : List (Nat × Nat)) (factorNum factorDen : Nat)
    (localBound : ∀ p ∈ pairs, p.1 * factorDen ≤ p.2 * factorNum) :
    product (pairs.map Prod.fst) * factorDen^pairs.length ≤
      product (pairs.map Prod.snd) * factorNum^pairs.length := by
  induction pairs with
  | nil => simp [product]
  | cons p rest ih =>
    have head := localBound p (by simp)
    have tail := ih (fun x hx => localBound x (by simp [hx]))
    have step := Nat.mul_le_mul head tail
    simpa [product, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using step

end NearClockCoding
