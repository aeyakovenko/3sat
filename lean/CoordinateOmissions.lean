import Std

namespace CoordinateOmissions

/-- Sum over all next-symbol choices. The multiplier at a node can depend on
    the complete revealed history, represented in reverse chronological order. -/
def productMass (alphabet : List Nat) (weight : List Nat → Nat → Nat) :
    Nat → List Nat → Nat
  | 0, _ => 1
  | steps+1, past =>
    (alphabet.map fun s => weight past s *
      productMass alphabet weight steps (s :: past)).sum

private theorem weightedSumBound (xs : List Nat) (w f : Nat → Nat) (b : Nat)
    (bound : ∀ x ∈ xs, f x ≤ b) :
    (xs.map fun x => w x * f x).sum ≤ (xs.map w).sum * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (bound x (by simp)))
      (ih fun y hy => bound y (by simp [hy]))

/-- Fixed-exposure-order product estimate, with common integral scaling.
    At a nonready node all weights can equal the scaling denominator. -/
theorem predictableProduct (alphabet : List Nat) (weight : List Nat → Nat → Nat)
    (cap : Nat) (normalize : ∀ past, (alphabet.map (weight past)).sum ≤ cap)
    (steps : Nat) (past : List Nat) :
    productMass alphabet weight steps past ≤ cap^steps := by
  induction steps generalizing past with
  | zero => simp [productMass]
  | succ steps ih =>
    rw [productMass]
    calc
      _ ≤ (alphabet.map (weight past)).sum * cap^steps :=
        weightedSumBound alphabet (weight past) _ _ (fun s _ => ih (s :: past))
      _ ≤ cap * cap^steps := Nat.mul_le_mul_right _ (normalize past)
      _ = cap^(steps+1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- Counting the first r elements in every set, allowing overlaps. The union
    can only be smaller than this concatenation, which retains duplicates. -/
theorem prefixesBound {α : Type} (family : List (List α)) (r : Nat) :
    (family.flatMap (List.take r)).length ≤ family.length * r := by
  induction family with
  | nil => simp
  | cons xs rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_take,
      List.length_cons, Nat.succ_mul]
    omega

end CoordinateOmissions
