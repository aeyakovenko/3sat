import Std

namespace MajoritySeam

inductive Bits : Nat → Type where
  | nil : Bits 0
  | cons {n} : Bool → Bits n → Bits (n + 1)

def Bits.weight : {n : Nat} → Bits n → Nat
  | _, .nil => 0
  | _, .cons b xs => (if b then 1 else 0) + xs.weight

def Bits.fill (bit : Bool) : (n : Nat) → Bits n
  | 0 => .nil
  | n + 1 => .cons bit (fill bit n)

def Bits.dist : {n : Nat} → Bits n → Bits n → Nat
  | _, .nil, .nil => 0
  | _, .cons a u, .cons b v => (if a = b then 0 else 1) + u.dist v

/-- The two branches represent `a + x₁·b` in multilinear algebraic normal form. -/
inductive ANF : Nat → Type where
  | constant : Bool → ANF 0
  | split {n} : ANF n → ANF n → ANF (n + 1)

def ANF.eval : {n : Nat} → ANF n → Bits n → Bool
  | _, .constant c, .nil => c
  | _, .split a b, .cons x xs => Bool.xor (a.eval xs) (x && b.eval xs)

def ANF.zero : {n : Nat} → ANF n → Prop
  | _, .constant c => c = false
  | _, .split a b => a.zero ∧ b.zero

def ANF.bounded : {n : Nat} → ANF n → Nat → Prop
  | _, .constant _, _ => True
  | _, .split a b, 0 => a.bounded 0 ∧ b.zero
  | _, .split a b, d + 1 => a.bounded (d + 1) ∧ b.bounded d

theorem eval_zero {n} (p : ANF n) (h : p.zero) (xs : Bits n) : p.eval xs = false := by
  induction p with
  | constant => cases xs; exact h
  | split a b ia ib =>
    cases xs with
    | cons x xs => simp [ANF.eval, ia h.1 xs, ib h.2 xs]

/-- The support of a nonzero degree-at-most-d polynomial meets the radius-d
    Hamming ball about *each* center. If its first derivative is nonzero,
    find that derivative in the radius-(d-1) ball and choose the first bit. -/
theorem every_ball {n} (p : ANF n) (d : Nat) (deg : p.bounded d)
    (live : ∃ x, p.eval x = true) (center : Bits n) :
    ∃ x, center.dist x ≤ d ∧ p.eval x = true := by
  classical
  induction p generalizing d with
  | constant =>
    obtain ⟨x, yes⟩ := live
    cases center; cases x
    exact ⟨.nil, Nat.zero_le _, yes⟩
  | split a b ia ib =>
    cases center with
    | cons bit tail =>
      by_cases changes : ∃ x, b.eval x = true
      · cases d with
        | zero =>
          obtain ⟨x, yes⟩ := changes
          have no := eval_zero b deg.2 x
          simp [yes] at no
        | succ k =>
          obtain ⟨x, close, yes⟩ := ib k deg.2 changes tail
          refine ⟨.cons (!(a.eval x)) x, ?_, ?_⟩
          · simp only [Bits.dist]; split <;> omega
          · cases value : a.eval x <;> simp [ANF.eval, value, yes]
      · have no (x) : b.eval x = false := by
          cases hv : b.eval x with
          | false => rfl
          | true => exact False.elim (changes ⟨x, hv⟩)
        have aBound : a.bounded d := by cases d <;> exact deg.1
        obtain ⟨v, yes⟩ := live
        cases v with
        | cons head rest =>
          have real : a.eval rest = true := by simpa [ANF.eval, no] using yes
          obtain ⟨x, close, val⟩ := ia d aBound ⟨rest, real⟩ tail
          exact ⟨.cons bit x, by simpa [Bits.dist] using close, by simp [ANF.eval, val, no]⟩

theorem extreme_centers {n} (x : Bits n) :
    (Bits.fill false n).dist x = x.weight ∧ (Bits.fill true n).dist x + x.weight = n := by
  induction x with
  | nil => decide
  | @cons n bit xs ih =>
    cases bit <;> simp only [Bits.fill, Bits.dist, Bits.weight, ↓reduceIte,
      Bool.false_eq_true, Bool.true_eq_false, Nat.zero_add] <;> omega

theorem majority_degree {k d} (p : ANF (2 * k + 1)) (deg : p.bounded d)
    (live : ∃ x, p.eval x = true) (sign : Prop)
    (mono : ∀ x, p.eval x = true → (k + 1 ≤ x.weight ↔ sign)) : k + 1 ≤ d := by
  classical
  by_cases yes : sign
  · obtain ⟨x, close, hx⟩ := every_ball p d deg live (.fill false _)
    have := (mono x hx).mpr yes
    rw [(extreme_centers x).1] at close
    omega
  · obtain ⟨x, close, hx⟩ := every_ball p d deg live (.fill true _)
    have light : ¬ k + 1 ≤ x.weight := fun heavy => yes ((mono x hx).mp heavy)
    have := (extreme_centers x).2
    omega

end MajoritySeam
