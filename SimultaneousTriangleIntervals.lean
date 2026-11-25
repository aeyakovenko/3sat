import Std

namespace SimultaneousTriangleIntervals

/-- Finite sums indexed from zero, avoiding a dependency on mathlib. -/
def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total f n + f n

theorem addTotal (f g : Nat → Nat) (n : Nat) :
    total (fun i => f i + g i) n = total f n + total g n := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp only [total, ih]; omega

theorem constTotal (v n : Nat) : total (fun _ => v) n = n * v := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp [total, ih, Nat.succ_mul]

theorem scaleTotal (q : Nat) (f : Nat → Nat) (n : Nat) :
    total (fun i => q * f i) n = q * total f n := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp [total, ih, Nat.mul_add]

theorem monoTotal (f g : Nat → Nat) (n : Nat) (h : ∀ i, i < n → f i ≤ g i) :
    total f n ≤ total g n := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

theorem swapTotal (f : Nat → Nat → Nat) (n m : Nat) :
    total (fun i => total (f i) m) n = total (fun j => total (fun i => f i j) n) m := by
  induction n with
  | zero => simp [total, constTotal]
  | succ n ih => simp only [total, ih, addTotal]

def mass (f : Nat → Nat → Nat) (q : Nat) := total (fun i => total (f i) q) q

/-- If three cyclic incidence tables cover every triple, their total mass
    is at least q squared. Tables may count events with multiplicity. -/
theorem triangleCover (f g h : Nat → Nat → Nat) (q : Nat) (hq : 0 < q)
    (cover : ∀ i < q, ∀ j < q, ∀ k < q, 1 ≤ f i j + g j k + h k i) :
    q * q ≤ mass f q + mass g q + mass h q := by
  have inner (i : Nat) (hi : i < q) (j : Nat) (hj : j < q) :
      q ≤ q * f i j + total (g j) q + total (fun k => h k i) q := by
    have hh := monoTotal _ _ q (cover i hi j hj)
    simpa only [constTotal, Nat.mul_one, addTotal] using hh
  have middle (i : Nat) (hi : i < q) :
      q*q ≤ q * total (f i) q + mass g q + q * total (fun k => h k i) q := by
    have hh := monoTotal _ _ q (inner i hi)
    simpa only [constTotal, addTotal, scaleTotal, mass] using hh
  have hh := monoTotal _ _ q middle
  simp only [constTotal, addTotal, scaleTotal, mass] at hh
  rw [swapTotal (fun i k => h k i)] at hh
  simp only [← Nat.mul_add] at hh
  exact Nat.le_of_mul_le_mul_left hh hq

/-- A simultaneous surviving triple exists below the square threshold. -/
theorem findTriangle (f g h : Nat → Nat → Nat) (q : Nat) (hq : 0 < q)
    (few : mass f q + mass g q + mass h q < q*q) :
    ∃ i < q, ∃ j < q, ∃ k < q, f i j = 0 ∧ g j k = 0 ∧ h k i = 0 := by
  apply Classical.byContradiction
  intro none
  apply (Nat.not_le_of_lt few)
  apply triangleCover f g h q hq
  intro i hi j hj k hk
  by_cases a : f i j = 0 <;> by_cases b : g j k = 0 <;> by_cases c : h k i = 0
  all_goals first | exact False.elim (none ⟨i, hi, j, hj, k, hk, a, b, c⟩) | omega

end SimultaneousTriangleIntervals
