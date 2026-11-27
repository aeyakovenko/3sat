import Std

namespace SparseFiberMoments

/-- A word of length n. The same type specifies a squarefree monomial
    by marking the coordinates present in its product. -/
def Word : Nat → Type
  | 0 => Unit
  | n + 1 => Bool × Word n

def degree : (n : Nat) → Word n → Nat
  | 0, _ => 0
  | n + 1, (b, m) => (if b then 1 else 0) + degree n m

def emptyMask : (n : Nat) → Word n
  | 0 => ()
  | n + 1 => (false, emptyMask n)

/-- Number of words in the set specified by its Boolean indicator. -/
def size : (n : Nat) → (Word n → Bool) → Nat
  | 0, f => if f () then 1 else 0
  | n + 1, f => size n (fun x => f (false, x)) + size n (fun x => f (true, x))

/-- Number of support words on which the marked monomial is one. -/
def overlap : (n : Nat) → Word n → (Word n → Bool) → Nat
  | 0, _, f => if f () then 1 else 0
  | n + 1, (true, m), f => overlap n m (fun x => f (true, x))
  | n + 1, (false, m), f =>
    overlap n m (fun x => f (false, x)) + overlap n m (fun x => f (true, x))

@[simp] theorem empty_degree (n : Nat) : degree n (emptyMask n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [degree, emptyMask, ih]

@[simp] theorem empty_overlap (n : Nat) (f : Word n → Bool) :
    overlap n (emptyMask n) f = size n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [emptyMask, overlap, size, ih]

theorem overlap_le_size (n : Nat) (m : Word n) (f : Word n → Bool) :
    overlap n m f ≤ size n f := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    obtain ⟨b, m⟩ := m
    have lo := ih m (fun x => f (false, x))
    have hi := ih m (fun x => f (true, x))
    cases b <;> simp only [overlap, size] <;> omega

def ZeroMoments (n d : Nat) (f : Word n → Bool) : Prop :=
  ∀ m : Word n, degree n m ≤ d → overlap n m f % 2 = 0

/-- The minimum nonzero weight of a vector orthogonal over F₂ to
    every squarefree monomial through degree d is at least 2^(d+1).
    This includes dimensions n ≤ d, in which no nonempty support qualifies. -/
theorem minimum_distance (n d : Nat) (f : Word n → Bool)
    (nonempty : 0 < size n f) (vanish : ZeroMoments n d f) :
    2 ^ (d + 1) ≤ size n f := by
  induction n generalizing d with
  | zero =>
    have total := vanish (emptyMask 0) (by simp)
    simp only [empty_overlap] at total
    cases b : f () <;> simp [size, b] at nonempty total
  | succ n ih =>
    have evenTotal := vanish (emptyMask (n+1)) (by simp)
    simp only [empty_overlap] at evenTotal
    cases d with
    | zero =>
      change 2 ≤ size (n+1) f
      omega
    | succ d =>
      let low : Word n → Bool := fun x => f (false, x)
      let high : Word n → Bool := fun x => f (true, x)
      change 0 < size n low + size n high at nonempty
      change 2 ^ (d+1+1) ≤ size n low + size n high
      have together (m : Word n) (bound : degree n m ≤ d+1) :
          (overlap n m low + overlap n m high) % 2 = 0 :=
        vanish (false, m) (by simpa [degree] using bound)
      by_cases emptyLow : size n low = 0
      · have highMoments : ZeroMoments n (d+1) high := by
          intro m bound
          have small := overlap_le_size n m low
          have total := together m bound
          omega
        have bound := ih (d+1) high (by omega) highMoments
        omega
      by_cases emptyHigh : size n high = 0
      · have lowMoments : ZeroMoments n (d+1) low := by
          intro m bound
          have small := overlap_le_size n m high
          have total := together m bound
          omega
        have bound := ih (d+1) low (by omega) lowMoments
        omega
      -- Both slices are nonempty. Multiplication by the first variable
      -- tests the high slice; subtracting it from the full test gives the low slice.
      have highMoments : ZeroMoments n d high := by
        intro m bound
        exact vanish (true, m) (by simp [degree]; omega)
      have lowMoments : ZeroMoments n d low := by
        intro m bound
        have total := together m (by omega)
        have part := highMoments m bound
        omega
      have first := ih d low (by omega) lowMoments
      have second := ih d high (by omega) highMoments
      rw [Nat.pow_succ]
      omega

/-- A smaller nonempty support has an odd low-degree moment. -/
theorem odd_moment_of_sparse (n d : Nat) (f : Word n → Bool)
    (nonempty : 0 < size n f) (small : size n f < 2 ^ (d+1)) :
    ∃ m : Word n, degree n m ≤ d ∧ overlap n m f % 2 = 1 := by
  apply Classical.byContradiction
  intro missing
  have vanish : ZeroMoments n d f := by
    intro m bound
    have absent : overlap n m f % 2 ≠ 1 := fun hit => missing ⟨m, bound, hit⟩
    omega
  exact (Nat.not_le_of_gt small) (minimum_distance n d f nonempty vanish)

end SparseFiberMoments
