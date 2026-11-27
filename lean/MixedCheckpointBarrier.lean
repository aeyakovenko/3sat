import Std

/-! Exact finite lower certificate for the mixed checkpoint rule. All profile
coordinates have denominator 12000. The balanced output can have a different
denominator, so it is compared by cross multiplication, without rounding. -/

namespace MixedCheckpointBarrier

def scale : Nat := 12000
def cutoff : Nat := 8619

def work : Nat → Nat
  | 0 => 3381
  | 1 => 1524
  | 2 => 858
  | 3 => 576
  | _ => 484

def publicFloor : Nat → Nat
  | 0 => 0
  | 1 => 3381
  | 2 => 4905
  | 3 => 5763
  | _ => 6339

/-- Check all rational scalings, successive prefix floors, the dominance
of the initial profile (1,0), and the strict opposite ordering of the two
envelope coordinates. -/
theorem catalogue :
    4000*cutoff = 2873*scale ∧
    4000*work 0 = 1127*scale ∧ 1000*work 1 = 127*scale ∧
    2000*work 2 = 143*scale ∧ 125*work 3 = 6*scale ∧ 3000*work 4 = 121*scale ∧
    publicFloor 0 = 0 ∧ work 0 ≤ scale ∧
    (∀ i : Fin 4, publicFloor (i.val+1) = publicFloor i.val + work i.val) ∧
    (∀ i j : Fin 5, i.val < j.val →
      work j.val < work i.val ∧ publicFloor i.val < publicFloor j.val) := by decide

/-- Moving the smaller work and larger floor to the front weakly reduces
both affected charge statistics; the times of later rows see the same sum. -/
theorem adjacentSwap {elapsed d f t g : Nat} (workOrder : t ≤ d) (floorOrder : f ≤ g) :
    max (elapsed+g) (elapsed+t+f) ≤ max (elapsed+f) (elapsed+d+g) ∧
    (elapsed+g)+(elapsed+t+f) ≤ (elapsed+f)+(elapsed+d+g) ∧
    elapsed+t+d = elapsed+d+t := by
  have upper := Nat.le_max_right (elapsed+f) (elapsed+d+g)
  exact ⟨Nat.max_le.mpr ⟨by omega, by omega⟩, by omega, by omega⟩

structure Prefix where
  length : Nat
  elapsed : Nat
  chargeSum : Nat
  chargeMax : Nat
  deriving DecidableEq

def empty : Prefix := ⟨0, 0, 0, 0⟩

def charge (p : Prefix) (i : Nat) : Nat := p.elapsed + publicFloor i

def appendRow (p : Prefix) (i : Nat) : Prefix :=
  ⟨p.length + 1, p.elapsed + work i, p.chargeSum + charge p i, max p.chargeMax (charge p i)⟩

def eligible (p : Prefix) (i : Nat) : Prop := charge p i < cutoff

instance (p : Prefix) (i : Nat) : Decidable (eligible p i) :=
  inferInstanceAs (Decidable (charge p i < cutoff))

/-- floor_i ≤ F and work_i ≤ max(E,F-c). For E we move k*c to the
left before comparing, so subtraction of natural numbers is never used. -/
def dominates (p : Prefix) (i : Nat) : Prop :=
  publicFloor i ≤ p.chargeMax ∧
    (work i + cutoff ≤ p.chargeMax ∨
      (p.length + 1) * work i + p.length * cutoff ≤ scale + p.chargeSum + p.elapsed)

instance (p : Prefix) (i : Nat) : Decidable (dominates p i) := by
  unfold dominates
  infer_instance

def hasDominator (p : Prefix) : Bool :=
  (List.range 5).any fun i => decide (dominates p i)

/-- Indices are nonincreasing from outer to inner. At each append the full
prefix charge must be strictly below the cutoff. -/
def Admissible (largest : Nat) (p : Prefix) : List Nat → Prop
  | [] => True
  | i :: tail => i ≤ largest ∧ eligible p i ∧ Admissible i (appendRow p i) tail

def finish (p : Prefix) (indices : List Nat) : Prefix := indices.foldl appendRow p

theorem minimumWork (i : Nat) : 484 ≤ work i := by
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ i =>
        cases i <;> simp [work]

theorem elapsedLower (indices : List Nat) (p : Prefix) :
    p.elapsed + indices.length * 484 ≤ (finish p indices).elapsed := by
  induction indices generalizing p with
  | nil => simp [finish]
  | cons i tail ih =>
    have h := ih (appendRow p i)
    have hw := minimumWork i
    change p.elapsed + work i + tail.length * 484 ≤ (finish (appendRow p i) tail).elapsed at h
    change p.elapsed + (tail.length+1)*484 ≤ (finish (appendRow p i) tail).elapsed
    rw [Nat.add_mul]
    omega

theorem noFurtherRow {indices : List Nat} (long : 18 ≤ indices.length) (i : Nat) :
    ¬ eligible (finish empty indices) i := by
  have h := elapsedLower indices empty
  simp only [show empty.elapsed = 0 from rfl, Nat.zero_add] at h
  unfold eligible charge cutoff
  omega

/-- The zero-fuel branch checks that *no* eligible child has been omitted.
All other branches verify the newly appended nonempty prefix and recurse. -/
def checkTree : Nat → Nat → Prefix → Bool
  | 0, largest, p =>
    (List.range (largest+1)).all fun i => decide (¬ eligible p i)
  | fuel+1, largest, p =>
    (List.range (largest+1)).all fun i =>
      if eligible p i then
        hasDominator (appendRow p i) && checkTree fuel i (appendRow p i)
      else true

def countTree : Nat → Nat → Prefix → Nat
  | 0, _, _ => 0
  | fuel+1, largest, p =>
    ((List.range (largest+1)).map fun i =>
      if eligible p i then 1 + countTree fuel i (appendRow p i) else 0).sum

/-- A successful search implies domination on every nonempty admissible
extension, including lists initially supplied without any length bound. -/
theorem coversAll (fuel largest : Nat) (p : Prefix) (indices : List Nat)
    (pass : checkTree fuel largest p = true) (valid : Admissible largest p indices)
    (nonempty : indices ≠ []) : hasDominator (finish p indices) = true := by
  induction fuel generalizing largest p indices with
  | zero =>
    cases indices with
    | nil => exact False.elim (nonempty rfl)
    | cons i tail =>
      have mem : i ∈ List.range (largest+1) := List.mem_range.mpr (by have := valid.1; omega)
      have h := List.all_eq_true.mp pass i mem
      exact False.elim (of_decide_eq_true h valid.2.1)
  | succ fuel ih =>
    cases indices with
    | nil => exact False.elim (nonempty rfl)
    | cons i tail =>
      obtain ⟨hsize, good, tailValid⟩ := valid
      have mem : i ∈ List.range (largest+1) := List.mem_range.mpr (by omega)
      have h := List.all_eq_true.mp pass i mem
      simp only [if_pos good, Bool.and_eq_true] at h
      cases tail with
      | nil => exact h.1
      | cons j rest => exact ih i (appendRow p i) (j::rest) h.2 tailValid (by simp)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem verifiedTree : checkTree 18 4 empty = true := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem verifiedCount : countTree 18 4 empty = 718 := by decide

theorem orderedBarrier {indices : List Nat}
    (valid : Admissible 4 empty indices) (nonempty : indices ≠ []) :
    ∃ i, i < 5 ∧ dominates (finish empty indices) i := by
  have check := coversAll 18 4 empty indices verifiedTree valid nonempty
  obtain ⟨i, hi, hd⟩ := List.any_eq_true.mp check
  exact ⟨i, List.mem_range.mp hi, of_decide_eq_true hd⟩

end MixedCheckpointBarrier
