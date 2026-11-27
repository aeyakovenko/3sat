import Std

namespace FerrersMatrixCompression

/-- A row of a compressed missing set is its initial interval of this width.
    Rows and columns are indexed from zero. -/
def area (width : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => area width n + width n

private theorem finalRows (width : Nat → Nat)
    (mono : ∀ i i', i ≤ i' → width i ≤ width i') (i d : Nat) :
    (d-i) * width i ≤ area width d := by
  induction d with
  | zero => simp [area]
  | succ d ih =>
    by_cases h : i ≤ d
    · have h₁ : d+1-i = (d-i)+1 := by omega
      rw [h₁, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add ih (mono i d h)
    · have h₁ : d+1-i = 0 := by omega
      simp [h₁]

/-- A missing cell forces the whole rectangle of later rows and earlier columns. -/
theorem missingRectangle (width : Nat → Nat)
    (mono : ∀ i i', i ≤ i' → width i ≤ width i')
    (d i j : Nat) (missing : j < width i) : (d-i)*(j+1) ≤ area width d :=
  Nat.le_trans (Nat.mul_le_mul_left (d-i) missing) (finalRows width mono i d)

/-- Trim `a` final rows and `b` initial columns. Every remaining cell is
    occupied once the smallest rectangle a hole could force exceeds the area. -/
theorem trimmedRectangle (width : Nat → Nat)
    (mono : ∀ i i', i ≤ i' → width i ≤ width i') {d a b p i j : Nat}
    (budget : area width d ≤ p) (enough : p < (a+1)*(b+1))
    (row : i < d-a) (col : b ≤ j) : width i ≤ j := by
  by_cases h : j < width i
  · have hole := missingRectangle width mono d i j h
    have sides := Nat.mul_le_mul (show a+1 ≤ d-i by omega) (show b+1 ≤ j+1 by omega)
    omega
  · omega

/-- An elementary floor square root; only its bounding inequalities are used. -/
def floorRoot : Nat → Nat
  | 0 => 0
  | n+1 => let r := floorRoot n; if (r+1)*(r+1) ≤ n+1 then r+1 else r

theorem floorRootSpec (n : Nat) :
    floorRoot n * floorRoot n ≤ n ∧ n < (floorRoot n+1)*(floorRoot n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [floorRoot]
    split
    · rename_i h
      refine ⟨h, ?_⟩
      have nxt : (floorRoot n+1)*(floorRoot n+1) <
          (floorRoot n+1+1)*(floorRoot n+1+1) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
        omega
      omega
    · rename_i h
      exact ⟨by omega, by omega⟩

/-- The square on indices `r,…,d−r−1` survives for `r = ⌊√p⌋`.
    The statement is vacuous when the interval is empty. -/
theorem centerSquare (width : Nat → Nat)
    (mono : ∀ i i', i ≤ i' → width i ≤ width i') {d p i j : Nat}
    (budget : area width d ≤ p)
    (row : i < d-floorRoot p) (col : floorRoot p ≤ j) : width i ≤ j :=
  trimmedRectangle width mono budget (floorRootSpec p).2 row col

end FerrersMatrixCompression
