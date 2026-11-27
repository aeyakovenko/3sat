import Std

namespace PackedStableCell

/-- A single pass of packed least-significant-digit radix sort. The packing
changes only the implementation of these two order-preserving filters. -/
def radixPass (digit : Nat → Bool) (key : α → Nat) (xs : List α) : List α :=
  xs.filter (fun v => !(digit (key v))) ++ xs.filter (fun v => digit (key v))

def cell (key : α → Nat) (a : Nat) (xs : List α) : List α :=
  xs.filter (fun v => decide (key v = a))

private theorem filter_then (p q : α → Bool) (xs : List α) :
    (xs.filter p).filter q = xs.filter (fun a => p a && q a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h₁ : p x <;> cases h₂ : q x <;> simp [h₁, h₂, ih]

private theorem filter_ext (xs : List α) (p q : α → Bool)
    (h : ∀ a, p a = q a) : xs.filter p = xs.filter q := by
  have eq : p = q := funext h
  rw [eq]

/-- Every stable pass preserves the exact chronological subsequence at each
address, including reads and writes in the same guest step. -/
theorem radix_cell (digit : Nat → Bool) (key : α → Nat) (a : Nat) (xs : List α) :
    cell key a (radixPass digit key xs) = cell key a xs := by
  simp only [cell, radixPass, List.filter_append, filter_then]
  cases hv : digit a with
  | false =>
    have h₁ : xs.filter (fun v => !(digit (key v)) && decide (key v = a)) =
        xs.filter (fun v => decide (key v = a)) := by
      apply filter_ext
      intro v
      by_cases h : key v = a <;> simp [h,hv]
    have h₂ : xs.filter (fun v => digit (key v) && decide (key v = a)) =
        xs.filter (fun _ => false) := by
      apply filter_ext
      intro v
      by_cases h : key v = a <;> simp [h,hv]
    rw [h₁,h₂]
    simp
  | true =>
    have h₁ : xs.filter (fun v => !(digit (key v)) && decide (key v = a)) =
        xs.filter (fun _ => false) := by
      apply filter_ext
      intro v
      by_cases h : key v = a <;> simp [h,hv]
    have h₂ : xs.filter (fun v => digit (key v) && decide (key v = a)) =
        xs.filter (fun v => decide (key v = a)) := by
      apply filter_ext
      intro v
      by_cases h : key v = a <;> simp [h,hv]
    rw [h₁,h₂]
    simp

theorem passes_cell (digits : List (Nat → Bool)) (key : α → Nat) (a : Nat)
    (xs : List α) :
    cell key a (digits.foldl (fun s d => radixPass d key s) xs) = cell key a xs := by
  induction digits generalizing xs with
  | nil => rfl
  | cons d ds ih =>
    rw [List.foldl_cons, ih, radix_cell]

#print axioms passes_cell

end PackedStableCell
