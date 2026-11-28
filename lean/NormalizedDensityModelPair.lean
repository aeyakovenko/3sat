import Std

namespace NormalizedDensityModelPair

def blockClause (f x : Fin 8) : Bool := x.val != f.val

/-- Every ternary block with a single forbidden pattern admits a pair that
    differs on all three bits. -/
theorem complementary_block : ∀ f : Fin 8, ∃ x y : Fin 8,
    x.val ^^^ y.val = 7 ∧ blockClause f x ∧ blockClause f y := by
  intro f
  by_cases h : f.val = 0 ∨ f.val = 7
  · refine ⟨1,6,rfl,?_,?_⟩ <;> simp [blockClause] <;> omega
  · refine ⟨0,7,rfl,?_,?_⟩ <;> simp [blockClause] <;> omega

theorem lost_pair_atom {good total : Nat} (missing : good < total) (small : total ≤ 49) :
    good * 49 ≤ total * 48 := by omega

theorem narrowed_block {good total : Nat} (missing : good < total) (small : total ≤ 7) :
    good * 7 ≤ total * 6 := by omega

def prodGood : List (Nat × Nat) → Nat
  | [] => 1
  | p :: ps => p.1 * prodGood ps

def prodTotal : List (Nat × Nat) → Nat
  | [] => 1
  | p :: ps => p.2 * prodTotal ps

/-- Product-measure loss for disjoint block constraints.  Cross multiplication
    avoids rounding when each local event has its own denominator. -/
theorem product_loss (a b : Nat) (xs : List (Nat × Nat))
    (each : ∀ x ∈ xs, x.1 * a ≤ x.2 * b) :
    prodGood xs * a^xs.length ≤ prodTotal xs * b^xs.length := by
  induction xs with
  | nil => simp [prodGood,prodTotal]
  | cons x xs ih =>
    have h := each x (by simp)
    have tail := ih (by intro y hy; exact each y (by simp [hy]))
    simp only [List.length_cons,Nat.pow_succ]
    change (x.1 * prodGood xs) * (a ^ xs.length * a) ≤
      (x.2 * prodTotal xs) * (b ^ xs.length * b)
    calc
      _ = (x.1 * a) * (prodGood xs * a ^ xs.length) := by ac_rfl
      _ ≤ (x.2 * b) * (prodTotal xs * b ^ xs.length) := Nat.mul_le_mul h tail
      _ = _ := by ac_rfl

/-- Two old models both missing a neighbor must agree on every literal of the
    changed four-variable pattern. -/
theorem missed_edit : ∀ o₁ t₁ a₁ b₁ o₂ t₂ a₂ b₂ : Bool,
    (o₁ || a₁ || b₁) → !(t₁ || a₁ || b₁) →
    (o₂ || a₂ || b₂) → !(t₂ || a₂ || b₂) →
    o₁ = o₂ ∧ t₁ = t₂ ∧ a₁ = a₂ ∧ b₁ = b₂ := by decide +kernel

end NormalizedDensityModelPair
