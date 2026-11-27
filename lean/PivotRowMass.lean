import Std

namespace PivotRowMass

/-- Enumerate all bit rows of an exact dimension, including the zero row. -/
def rows : Nat → List (List Bool)
  | 0 => [[]]
  | d+1 => (rows d).map (false :: ·) ++ (rows d).map (true :: ·)

theorem rowCount (d : Nat) : (rows d).length = 2^d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [rows, ih, Nat.pow_succ]; omega

theorem rowMembership (d : Nat) (xs : List Bool) : xs ∈ rows d ↔ xs.length = d := by
  induction d generalizing xs with
  | zero => simp [rows]
  | succ d ih =>
    cases xs with
    | nil => simp [rows]
    | cons b xs => cases b <;> simp [rows, ih]

theorem distinctRows (d : Nat) : (rows d).Nodup := by
  induction d with
  | zero => simp [rows]
  | succ d ih =>
    change List.Pairwise (· ≠ ·) (_ ++ _)
    rw [List.pairwise_append]
    constructor
    · simpa [List.pairwise_map] using ih
    constructor
    · simpa [List.pairwise_map] using ih
    · intro a ha b hb
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
      simp

/-- pivot j means that the first set position is j+1 in one-based notation. -/
def pivot : Nat → List Bool → Bool
  | _, [] => false
  | 0, b :: _ => b
  | _+1, true :: _ => false
  | j+1, false :: xs => pivot j xs

theorem cellCount (d j : Nat) (within : j < d) :
    (rows d).countP (pivot j) = 2^(d-(j+1)) := by
  induction d generalizing j with
  | zero => omega
  | succ d ih =>
    cases j with
    | zero => simp [rows, Function.comp_def, pivot, rowCount]
    | succ j =>
      have h := ih j (by omega)
      simpa [rows, Function.comp_def, pivot] using h

private theorem nonzeroCount (d : Nat) : (rows d).countP (fun x => x.any id) = 2^d-1 := by
  induction d with
  | zero => simp [rows]
  | succ d ih =>
    have pos := Nat.two_pow_pos d
    simp [rows, Function.comp_def, rowCount, Nat.pow_succ] at *
    omega

/-- There is a set bit, and the first J positions all vanish. -/
def late : Nat → List Bool → Bool
  | 0, xs => xs.any id
  | _+1, [] => false
  | _+1, true :: _ => false
  | j+1, false :: xs => late j xs

theorem tailCount (d J : Nat) : (rows d).countP (late J) = 2^(d-J)-1 := by
  induction J generalizing d with
  | zero => simpa [late] using nonzeroCount d
  | succ J ih =>
    cases d with
    | zero => simp [rows, late]
    | succ d => simpa [rows, Function.comp_def, late] using ih d

/-- Relative to the uniform distribution on nonzero rows, the tail has
    probability at most 2^(-J), with all denominators cleared. This also
    covers J greater than the dimension. -/
theorem uniformNonzeroTail (d J : Nat) :
    2^J * (rows d).countP (late J) ≤ (rows d).countP (fun x => x.any id) := by
  rw [tailCount, nonzeroCount]
  by_cases h : J ≤ d
  · have eq : 2^J * 2^(d-J) = 2^d := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [Nat.mul_sub, Nat.mul_one, eq]
    have hp := Nat.two_pow_pos J
    omega
  · have hz : d-J=0 := by omega
    simp [hz]

def early (J : Nat) (row : List Bool) : Bool := (row.take J).any id

private theorem partitionStep (J : Nat) (row : List Bool) :
    early (J+1) row = (early J row || pivot J row) ∧
      (early J row = true → pivot J row = false) := by
  induction J generalizing row with
  | zero =>
    cases row with
    | nil => simp [early, pivot]
    | cons x xs => cases x <;> simp [early, pivot]
  | succ J ih =>
    cases row with
    | nil => simp [early, pivot]
    | cons b xs =>
      cases b with
      | false => exact ih xs
      | true => simp [early, pivot]

/-- Entry weights are arbitrary integer masses on rows, including zero
    weights and repeated rows, after choosing one denominator. -/
def mass (pool : List (List Bool × Nat)) (p : List Bool → Bool) : Nat :=
  (pool.map (fun e => if p e.1 then e.2 else 0)).sum

private theorem massStep (pool : List (List Bool × Nat)) (J : Nat) :
    mass pool (early (J+1)) = mass pool (early J) + mass pool (pivot J) := by
  induction pool with
  | nil => simp [mass]
  | cons h t ih =>
    have ⟨part,sep⟩ := partitionStep J h.1
    cases a : early J h.1 <;> cases b : pivot J h.1 <;>
      simp [mass, part, a, b] at * <;> omega

private theorem peak (f : Nat → Nat) (k : Nat) :
    ∃ j ≤ k, ∀ i ≤ k, f i ≤ f j := by
  induction k with
  | zero =>
    refine ⟨0,by omega,?_⟩
    intro i hi
    have eq : i = 0 := by omega
    rw [eq]
    exact Nat.le_refl _
  | succ k ih =>
    obtain ⟨j,hj,hp⟩ := ih
    by_cases h : f j ≤ f (k+1)
    · refine ⟨k+1,by omega,?_⟩
      intro i hi
      by_cases eq : i=k+1
      · simp [eq]
      · exact Nat.le_trans (hp i (by omega)) h
    · refine ⟨j,by omega,?_⟩
      intro i hi
      by_cases eq : i=k+1
      · rw [eq]
        omega
      · exact hp i (by omega)

private theorem earlyBound (pool : List (List Bool × Nat)) (J cap : Nat)
    (h : ∀ i < J, mass pool (pivot i) ≤ cap) : mass pool (early J) ≤ J*cap := by
  induction J with
  | zero =>
    unfold mass
    simp [early]
    induction pool with
    | nil => rfl
    | cons e es ih => simpa using ih (by simp)
  | succ J ih =>
    rw [massStep, Nat.succ_mul]
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h J (by omega))

/-- If the first J cells carry half the designated total mass, at least
    one of them has mass at least total/(2J). Its one-based pivot is j+1. -/
theorem weightedPivot (pool : List (List Bool × Nat)) (J total : Nat) (nonempty : 0 < J)
    (half : total ≤ 2 * mass pool (early J)) :
    ∃ j < J, total ≤ (2*J) * mass pool (pivot j) := by
  obtain ⟨j,hj,hp⟩ := peak (fun i => mass pool (pivot i)) (J-1)
  refine ⟨j,by omega,?_⟩
  have bound := earlyBound pool J (mass pool (pivot j)) (fun i hi => hp i (by omega))
  rw [Nat.mul_assoc]
  exact Nat.le_trans half (Nat.mul_le_mul_left _ bound)

end PivotRowMass
