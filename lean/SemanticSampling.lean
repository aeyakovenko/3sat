import Std

namespace SemanticSampling

/-- Integer-valued scores on a finite pool with repeated observations allowed. -/
def total (f : Nat → Int) : List Nat → Int
  | [] => 0
  | x :: xs => f x + total f xs

private theorem total_add (f g : Nat → Int) (xs : List Nat) :
    total (fun x => f x + g x) xs = total f xs + total g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [total, ih]
    omega

private theorem total_scale (k : Int) (f : Nat → Int) (xs : List Nat) :
    total (fun x => k * f x) xs = k * total f xs := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Int.mul_add]

private theorem total_zero (xs : List Nat) : total (fun _ => 0) xs = 0 := by
  induction xs <;> simp_all [total]

abbrev Term := Int × Nat

def evaluate : List Term → Nat → Int
  | [], _ => 0
  | (k, d) :: ts, x => k * (x : Int) ^ d + evaluate ts x

/-- Scaled equality of moments through a degree bound transfers arbitrarily
signed polynomial scores. Clearing rational denominators is allowed. -/
theorem equalPolynomialTotals (p q : List Nat) (α β : Int) (cut : Nat)
    (moments : ∀ d ≤ cut,
      α * total (fun x => (x : Int)^d) p = β * total (fun x => (x : Int)^d) q)
    (terms : List Term) (degree : ∀ term ∈ terms, term.2 ≤ cut) :
    α * total (evaluate terms) p = β * total (evaluate terms) q := by
  induction terms with
  | nil => simp [evaluate, total_zero]
  | cons term terms ih =>
    obtain ⟨k, d⟩ := term
    have ok := moments d (degree (k,d) (by simp))
    have rest := ih (fun m hm => degree m (by simp [hm]))
    change α * total (fun x => k * (x : Int)^d + evaluate terms x) p =
      β * total (fun x => k * (x : Int)^d + evaluate terms x) q
    rw [total_add, total_add, total_scale, total_scale, Int.mul_add, Int.mul_add, rest]
    have left : α * (k * total (fun x => (x : Int)^d) p) =
        k * (α * total (fun x => (x : Int)^d) p) := by ac_rfl
    have right : β * (k * total (fun x => (x : Int)^d) q) =
        k * (β * total (fun x => (x : Int)^d) q) := by ac_rfl
    rw [left, right, ok]

def highCount (threshold : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => (if threshold ≤ x then 1 else 0) + highCount threshold xs

private theorem lowerScore (P : Nat → Int) (high : Nat) (floor : Int) (xs : List Nat)
    (nonneg : ∀ x ∈ xs, 0 ≤ P x) (large : ∀ x ∈ xs, high ≤ x → floor ≤ P x) :
    (highCount high xs : Int) * floor ≤ total P xs := by
  induction xs with
  | nil => simp [highCount, total]
  | cons x xs ih =>
    have tail := ih (fun z hz => nonneg z (by simp [hz]))
      (fun z hz => large z (by simp [hz]))
    by_cases h : high ≤ x
    · have here := large x (by simp) h
      simp [highCount, total, h, Int.add_mul]
      omega
    · have here := nonneg x (by simp)
      simp [highCount, total, h]
      omega

private theorem upperScore (P : Nat → Int) (cap : Int) (xs : List Nat)
    (small : ∀ x ∈ xs, P x ≤ cap) : total P xs ≤ (xs.length : Int) * cap := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have here := small x (by simp)
    have tail := ih (fun z hz => small z (by simp [hz]))
    simp [total, Int.add_mul]
    omega

/-- Nonnegative-on-support score, bounded on low accuracies and large at
high accuracies. One strict mass inequality forces an improved replacement. -/
theorem extractAccuracy (actual replacements : List Nat) (P : Nat → Int)
    (a b : Nat) (floor cap α β : Int) (ha : 0 ≤ α) (hb : 0 ≤ β)
    (same : α * total P actual = β * total P replacements)
    (nonneg : ∀ x ∈ actual, 0 ≤ P x)
    (high : ∀ x ∈ actual, b ≤ x → floor ≤ P x)
    (low : ∀ x ∈ replacements, x ≤ a → P x ≤ cap)
    (strict : β * ((replacements.length : Int) * cap) <
      α * ((highCount b actual : Int) * floor)) :
    ∃ x ∈ replacements, a < x := by
  apply Classical.byContradiction
  intro fails
  have small : ∀ x ∈ replacements, P x ≤ cap := by
    intro x hx
    apply low x hx
    by_cases le : x ≤ a
    · exact le
    · exact False.elim (fails ⟨x, hx, by omega⟩)
  have l := Int.mul_le_mul_of_nonneg_left (lowerScore P b floor actual nonneg high) ha
  have u := Int.mul_le_mul_of_nonneg_left (upperScore P cap replacements small) hb
  omega

end SemanticSampling
