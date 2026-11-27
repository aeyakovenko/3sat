import Std

namespace SparseForecastEquations

/-- Full truth table, split at the last coordinate. -/
def Table : Nat → Type
  | 0 => Bool
  | n+1 => Table n × Table n

def add : {n : Nat} → Table n → Table n → Table n
  | 0, a, b => a ^^ b
  | _+1, (a,b), (c,d) => (add a c, add b d)

def origin : {n : Nat} → Table n → Bool
  | 0, a => a
  | _+1, (a,_) => origin a

def weight : {n : Nat} → Table n → Nat
  | 0, a => (a : Bool).toNat
  | _+1, (a,b) => weight a + weight b

/-- ANF of a pair of faces consists of the zero face and the Boolean derivative. -/
def sparsity : {n : Nat} → Table n → Nat
  | 0, a => (a : Bool).toNat
  | _+1, (a,b) => sparsity a + sparsity (add a b)

private theorem origin_add {n} (a b : Table n) :
    origin (add a b) = (origin a ^^ origin b) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih a.1 b.1

private theorem cancel {n} (a b : Table n) : add a (add a b) = b := by
  induction n with
  | zero => cases a <;> cases b <;> rfl
  | succ n ih =>
    exact Prod.ext (ih a.1 b.1) (ih a.2 b.2)

private theorem interchange {n} (a b c d : Table n) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  induction n with
  | zero => cases a <;> cases b <;> cases c <;> cases d <;> rfl
  | succ n ih =>
    exact Prod.ext (ih a.1 b.1 c.1 d.1) (ih a.2 b.2 c.2 d.2)

private theorem weight_add {n} (a b : Table n) :
    weight (add a b) ≤ weight a + weight b := by
  induction n with
  | zero => cases a <;> cases b <;> decide
  | succ n ih =>
    change weight (add a.1 b.1) + weight (add a.2 b.2) ≤
      weight a.1 + weight a.2 + (weight b.1 + weight b.2)
    have h₁ := ih a.1 b.1
    have h₂ := ih a.2 b.2
    omega

private theorem sparsity_add {n} (a b : Table n) :
    sparsity (add a b) ≤ sparsity a + sparsity b := by
  induction n with
  | zero => cases a <;> cases b <;> decide
  | succ n ih =>
    change sparsity (add a.1 b.1) +
      sparsity (add (add a.1 b.1) (add a.2 b.2)) ≤
      sparsity a.1 + sparsity (add a.1 a.2) +
      (sparsity b.1 + sparsity (add b.1 b.2))
    rw [interchange a.1 b.1 a.2 b.2]
    have h₁ := ih a.1 b.1
    have h₂ := ih (add a.1 a.2) (add b.1 b.2)
    omega

/-- Uniform binary case of the sparse nonzero constant-term inequality. -/
theorem support_times_sparsity {n} (f : Table n) (h : origin f = true) :
    2^n ≤ weight f * sparsity f := by
  induction n with
  | zero =>
    cases f <;> first | contradiction | decide
  | succ n ih =>
    rcases f with ⟨a,b⟩
    change origin a = true at h
    change 2^(n+1) ≤ (weight a + weight b) * (sparsity a + sparsity (add a b))
    have ha := ih a h
    cases hd : origin (add a b) with
    | false =>
      have hb : origin b = true := by
        rw [origin_add, h] at hd
        cases hh : origin b <;> simp_all
      have hbBound := ih b hb
      have hSb := sparsity_add a (add a b)
      rw [cancel] at hSb
      have ca := Nat.mul_le_mul_left (weight a) (Nat.le_add_right (sparsity a) (sparsity (add a b)))
      have cb := Nat.mul_le_mul_left (weight b) hSb
      rw [Nat.add_mul, Nat.pow_succ]
      omega
    | true =>
      have hdBound := ih (add a b) hd
      have ca := Nat.mul_le_mul_right (sparsity a) (Nat.le_add_right (weight a) (weight b))
      have cd := Nat.mul_le_mul_right (sparsity (add a b)) (weight_add a b)
      rw [Nat.mul_add, Nat.pow_succ]
      omega

end SparseForecastEquations
