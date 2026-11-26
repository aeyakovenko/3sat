import Std

namespace HalfSubsetSyndromes

/-- Only the first n coordinates of a mask are used. -/
def weight : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, a => weight n a + (if a n then 1 else 0)

/-- A row vector may have any coordinate type. Its sum is over F₂. -/
def rowSum {ι : Type} (rows : Nat → ι → Bool) : Nat → (Nat → Bool) → ι → Bool
  | 0, _, _ => false
  | n + 1, a, j => Bool.xor (rowSum rows n a j) (a n && rows n j)

theorem weight_xor_le (n : Nat) (a b : Nat → Bool) :
    weight n (fun i => Bool.xor (a i) (b i)) ≤ weight n a + weight n b := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    cases ha : a n <;> cases hb : b n <;> simp [weight, ha, hb] <;> omega

theorem rowSum_xor {ι : Type} (rows : Nat → ι → Bool)
    (n : Nat) (a b : Nat → Bool) (j : ι) :
    rowSum rows n (fun i => Bool.xor (a i) (b i)) j =
      Bool.xor (rowSum rows n a j) (rowSum rows n b j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rowSum, ih]
    cases rowSum rows n a j <;> cases rowSum rows n b j <;>
      cases a n <;> cases b n <;> cases rows n j <;> rfl

/-- No nonempty sum of at most 2h rows vanishes on every vector coordinate. -/
def NoSmallDependence {ι : Type} (rows : Nat → ι → Bool) (n h : Nat) : Prop :=
  ∀ a : Nat → Bool, weight n a ≤ 2 * h →
    (∀ j, rowSum rows n a j = false) → ∀ i, i < n → a i = false

theorem equal_small_sums {ι : Type} {rows : Nat → ι → Bool} {n h : Nat}
    (indep : NoSmallDependence rows n h) {a b : Nat → Bool}
    (ha : weight n a ≤ h) (hb : weight n b ≤ h)
    (same : rowSum rows n a = rowSum rows n b) :
    ∀ i, i < n → a i = b i := by
  let diff := fun i => Bool.xor (a i) (b i)
  have few : weight n diff ≤ 2 * h := by
    have bound := weight_xor_le n a b
    change weight n (fun i => Bool.xor (a i) (b i)) ≤ 2 * h
    omega
  have vanishes (j : ι) : rowSum rows n diff j = false := by
    rw [show rowSum rows n diff j = _ from rowSum_xor rows n a b j, same]
    cases rowSum rows n b j <;> rfl
  intro i hi
  have hz := indep diff few vanishes i hi
  cases h₁ : a i <;> cases h₂ : b i <;> simp_all [diff]

def extend {n : Nat} (a : Fin n → Bool) (i : Nat) : Bool :=
  if hi : i < n then a ⟨i, hi⟩ else false

/-- In particular, all the h-element subset sums are distinct. -/
theorem bounded_subset_sums_injective {ι : Type} {rows : Nat → ι → Bool} {n h : Nat}
    (indep : NoSmallDependence rows n h) :
    ∀ a b : { mask : Fin n → Bool // weight n (extend mask) ≤ h },
      rowSum rows n (extend a.val) = rowSum rows n (extend b.val) → a = b := by
  intro a b same
  apply Subtype.ext
  funext i
  have eqAt := equal_small_sums indep a.property b.property same i.val i.isLt
  simpa [extend, i.isLt] using eqAt

end HalfSubsetSyndromes
