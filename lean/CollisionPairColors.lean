import Std

namespace CollisionPairColors

/-- Two selected pair-witnesses give odd parity exactly when one is selected. -/
private theorem xor_true (a b : Bool) : Bool.xor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

private theorem nonzero_iff {I : Type} (x : I → Bool) :
    (∃ i, x i = true) ↔ x ≠ (fun _ => false) := by
  constructor
  · rintro ⟨i, hi⟩ eq
    have hz := congrFun eq i
    simp [hi] at hz
  · intro nonzero
    apply Classical.byContradiction
    intro absent
    apply nonzero
    funext i
    cases hi : x i with
    | false => rfl
    | true => exact False.elim (absent ⟨i, hi⟩)

private theorem differ_iff {I : Type} (x y : I → Bool) :
    (∃ i, Bool.xor (x i) (y i) = true) ↔ x ≠ y := by
  constructor
  · rintro ⟨i, hi⟩ eq
    exact (xor_true _ _).mp hi (congrFun eq i)
  · intro different
    apply Classical.byContradiction
    intro absent
    apply different
    funext i
    apply Classical.byContradiction
    intro h
    exact absent ⟨i, (xor_true _ _).mpr h⟩

/-- For single witnesses and permitted pairs of witnesses, data-independent
masks detect odd parity exactly when their vector labels are nonzero and
separate every permitted pair. In the duplicate-pair application the
witnesses are edges and the relation is disjointness. -/
theorem mask_characterization {Edge I : Type} (allowed : Edge → Edge → Prop)
    (label : Edge → I → Bool) :
    ((∀ e, ∃ i, label e i = true) ∧
     (∀ e f, allowed e f → ∃ i, Bool.xor (label e i) (label f i) = true)) ↔
    ((∀ e, label e ≠ (fun _ => false)) ∧
     (∀ e f, allowed e f → label e ≠ label f)) := by
  constructor
  · rintro ⟨single, pair⟩
    exact ⟨fun e => (nonzero_iff _).mp (single e),
      fun e f h => (differ_iff _ _).mp (pair e f h)⟩
  · rintro ⟨nonzero, separates⟩
    exact ⟨fun e => (nonzero_iff _).mpr (nonzero e),
      fun e f h => (differ_iff _ _).mpr (separates e f h)⟩

private theorem square_ge_self (b : Nat) : b ≤ b * b := by
  cases b with
  | zero => decide
  | succ k => exact Nat.le_mul_of_pos_right _ (by omega)

/-- At least b+3 remaining vertices have more edges than b triangles can cover. -/
theorem too_many_pairs (r b : Nat) (many : b + 3 ≤ r) :
    3 * b < r * (r - 1) / 2 := by
  have factors : (b + 3) * (b + 2) ≤ r * (r - 1) :=
    Nat.mul_le_mul many (by omega)
  have square := square_ge_self b
  simp only [Nat.add_mul, Nat.mul_add] at factors
  omega

/-- If at most a star centers have been deleted, and each of the b remaining
triangle classes covers at most three remaining edges, at least t-2 colors
were used. Natural subtraction here handles the smallest t as well. -/
theorem star_triangle_color_bound (t a b r : Nat)
    (remaining : t - a ≤ r) (coverage : r * (r - 1) / 2 ≤ 3 * b) :
    t - 2 ≤ a + b := by
  apply Classical.byContradiction
  intro few
  have many : b + 3 ≤ r := by omega
  exact (Nat.not_lt_of_ge coverage) (too_many_pairs r b many)

/-- A family with at most t-3 classes cannot meet those cover counts when t≥3. -/
theorem too_few_colors (t a b r : Nat) (large : 3 ≤ t) (few : a + b ≤ t - 3)
    (remaining : t - a ≤ r) (coverage : r * (r - 1) / 2 ≤ 3 * b) : False := by
  have necessary := star_triangle_color_bound t a b r remaining coverage
  omega

end CollisionPairColors
