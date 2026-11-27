import Std

namespace MatrixWitnessDivisibility

/-- Pascal's integer coefficients, extended by zero outside a row. -/
def coeff : Nat → Nat → Int
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => coeff n k + coeff n (k + 1)

/-- The truncated alternating sum, with positive sign on its final term. -/
def alternating (n : Nat) : Nat → Int
  | 0 => 0
  | k + 1 => coeff n k - alternating n k

theorem pascal_cancellation (n k : Nat) :
    alternating (n + 1) (k + 1) = coeff n k := by
  induction k with
  | zero => cases n <;> rfl
  | succ k ih =>
    simp only [alternating, coeff] at ih ⊢
    omega

/-- A table of frozen rows and a disjoint table of variable rows. -/
def combined {I J A : Type} (f : I → A) (g : J → A) : Sum I J → A
  | .inl i => f i
  | .inr j => g j

def distinctRows {I A : Type} (f : I → A) : Prop :=
  ∀ i j, f i = f j → i = j

theorem slice_exact {I J A : Type} (f : I → A) (g : J → A)
    (fixedDistinct : distinctRows f) (disjoint : ∀ i j, f i ≠ g j) :
    distinctRows (combined f g) ↔ distinctRows g := by
  constructor
  · intro allRows i j hij
    exact Sum.inr.inj (allRows (.inr i) (.inr j) hij)
  · intro active i j eq
    cases i with
    | inl u =>
      cases j with
      | inl v => exact congrArg Sum.inl (fixedDistinct u v eq)
      | inr v => exact False.elim (disjoint u v eq)
    | inr u =>
      cases j with
      | inl v => exact False.elim (disjoint v u eq.symm)
      | inr v => exact congrArg Sum.inr (active u v eq)

/-- If no function of a signature decides a Boolean predicate, a positive
and a negative input have exactly the same signature. -/
theorem collision_of_no_decoder {I A : Type} (answer : I → Bool) (sig : I → A)
    (noDecoder : ¬ ∃ f : A → Bool, ∀ x, f (sig x) = answer x) :
    ∃ x y, answer x = true ∧ answer y = false ∧ sig x = sig y := by
  classical
  apply Classical.byContradiction
  intro noPair
  apply noDecoder
  refine ⟨fun s => decide (∃ x, answer x = true ∧ sig x = s), ?_⟩
  intro y
  cases hy : answer y with
  | true =>
    apply decide_eq_true
    exact ⟨y, hy, rfl⟩
  | false =>
    apply decide_eq_false
    intro yes
    obtain ⟨x, hx, same⟩ := yes
    exact noPair ⟨x, y, hx, hy, same⟩

end MatrixWitnessDivisibility

namespace MatrixWitnessDivisibility.WitnessParity

/-- Pascal coefficients reduced modulo two. -/
def bitCoeff : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _+1 => false
  | _+1, 0 => true
  | n+1, k+1 => bitCoeff n k ^^ bitCoeff n (k+1)

theorem column_zero (n : Nat) : bitCoeff n 0 = true := by cases n <;> rfl

theorem doubling (n : Nat) :
    (∀ k, bitCoeff (2*n) (2*k) = bitCoeff n k) ∧
    (∀ k, bitCoeff (2*n) (2*k+1) = false) := by
  induction n with
  | zero =>
    constructor
    · intro k
      cases k <;> rfl
    · intro k
      rfl
  | succ n ih =>
    have ol (k : Nat) : bitCoeff (2*n+1) (2*k) = bitCoeff n k := by
      cases k with
      | zero => simp [column_zero]
      | succ k =>
        rw [show 2*(k+1)=2*k+1+1 by omega]
        simp only [bitCoeff, ih.2, Bool.false_xor]
        exact ih.1 (k+1)
    have oright (k : Nat) : bitCoeff (2*n+1) (2*k+1) = bitCoeff n k := by
      simp only [bitCoeff, ih.1, ih.2, Bool.xor_false]
    rw [show 2*(n+1)=2*n+1+1 by omega]
    constructor
    · intro k
      cases k with
      | zero => simp [column_zero]
      | succ k =>
        rw [show 2*(k+1)=2*k+1+1 by omega]
        simp only [bitCoeff, oright]
        rw [show 2*k+1+1=2*(k+1) by omega]
        simp only [ih.1, ih.2, Bool.xor_false, Bool.false_xor]
    · intro k
      simp only [bitCoeff, ol, oright, ih.1, ih.2, Bool.xor_false, Bool.xor_self]

/-- XOR of the coefficients in columns below the given truncation. -/
def scan (n : Nat) : Nat → Bool
  | 0 => false
  | k+1 => scan n k ^^ bitCoeff n k

theorem even_scan (n q : Nat) : scan (2*n) (2*q) = scan n q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2*(q+1)=2*q+1+1 by omega]
    simp only [scan, ih, (doubling n).1, (doubling n).2, Bool.xor_false]

theorem odd_scan (n q : Nat) : scan (2*n+1) (2*q) = false := by
  have pair (k : Nat) : bitCoeff (2*n+1) (2*k) = bitCoeff (2*n+1) (2*k+1) := by
    simp only [bitCoeff, (doubling n).1, (doubling n).2, Bool.xor_false]
    cases k with
    | zero => simp [column_zero]
    | succ k =>
      rw [show 2*(k+1)=2*k+1+1 by omega]
      simp only [bitCoeff, (doubling n).2, Bool.false_xor]
      exact (doubling n).1 (k+1)
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [show 2*(q+1)=2*q+1+1 by omega]
    simp only [scan, ih, pair q, Bool.false_xor, Bool.xor_self]

theorem parity_filter (m b : Nat) : scan m (2^b) = true ↔ 2^b ∣ m := by
  induction b generalizing m with
  | zero => simp [scan, column_zero]
  | succ b ih =>
    rw [Nat.pow_succ, Nat.mul_comm (2^b)]
    by_cases he : m % 2 = 0
    · have hm : m = 2*(m/2) := by omega
      rw [show scan m (2*2^b) = scan (2*(m/2)) (2*2^b) from congrArg (fun v => scan v (2*2^b)) hm, even_scan, ih]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, by rw [Nat.mul_assoc, ← ht, ← hm]⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, by rw [Nat.mul_assoc] at ht; omega⟩
    · have hm : m = 2*(m/2)+1 := by omega
      rw [show scan m (2*2^b) = scan (2*(m/2)+1) (2*2^b) from congrArg (fun v => scan v (2*2^b)) hm, odd_scan]
      constructor
      · intro bad
        contradiction
      · rintro ⟨t, ht⟩
        rw [Nat.mul_assoc] at ht
        omega

theorem boolPascal_reduces_integerPascal (n k : Nat) :
    bitCoeff n k = decide (MatrixWitnessDivisibility.coeff n k % 2 = 1) := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [bitCoeff, MatrixWitnessDivisibility.coeff, ih]
      let a := MatrixWitnessDivisibility.coeff n k
      let b := MatrixWitnessDivisibility.coeff n (k+1)
      change (decide (a % 2 = 1) ^^ decide (b % 2 = 1)) =
        decide ((a+b)%2=1)
      by_cases ha : a%2=1 <;> by_cases hb : b%2=1 <;>
        simp [ha, hb] <;> omega

end MatrixWitnessDivisibility.WitnessParity
