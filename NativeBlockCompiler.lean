import Std

namespace NativeBlockCompiler

/-- Successively computed named gates can use the prior wires, including the input. -/
def complete : List (List Bool → Bool) → List Bool → List Bool
  | [], _ => []
  | g :: gs, env => g env :: complete gs (g env :: env)

def consistent : List (List Bool → Bool) → List Bool → List Bool → Prop
  | [], _, out => out = []
  | _ :: _, _, [] => False
  | g :: gs, env, b :: bs => b = g env ∧ consistent gs (b :: env) bs

theorem consistent_iff_complete (gs : List (List Bool → Bool)) (env out : List Bool) :
    consistent gs env out ↔ out = complete gs env := by
  induction gs generalizing env out with
  | nil => rfl
  | cons g gs ih =>
    cases out with
    | nil => simp [consistent, complete]
    | cons b bs =>
      simp only [consistent, complete, List.cons.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, (ih _ _).mp h⟩
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, (ih _ _).mpr h⟩

theorem selected_library_row {H L : Type} (f : H → L → Prop) (a : H) (b : L) :
    (∃ i j, i = a ∧ j = b ∧ f i j) ↔ f a b := by
  constructor
  · rintro ⟨i, j, rfl, rfl, h⟩
    exact h
  · intro h
    exact ⟨a, b, rfl, rfl, h⟩

/-- Fold one local mask into each bit, from the low end upwards. -/
def triangular : List (List Bool → Bool) → List Bool → List Bool → List Bool
  | m :: ms, lowBits, b :: bs =>
    (b != m lowBits) :: triangular ms (b :: lowBits) bs
  | _, _, _ => []

def untriangular : List (List Bool → Bool) → List Bool → List Bool → List Bool
  | m :: ms, lowBits, y :: ys =>
    let b := y != m lowBits
    b :: untriangular ms (b :: lowBits) ys
  | _, _, _ => []

private theorem mask_cancel (b m : Bool) : ((b != m) != m) = b := by
  cases b <;> cases m <;> rfl

theorem undo_triangular (ms : List (List Bool → Bool)) (p x : List Bool)
    (lengths : ms.length = x.length) :
    untriangular ms p (triangular ms p x) = x := by
  induction ms generalizing p x with
  | nil => cases x <;> simp_all [triangular, untriangular]
  | cons m ms ih =>
    cases x with
    | nil => simp at lengths
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp [triangular, untriangular, mask_cancel, ih _ _ lengths]

theorem redo_triangular (ms : List (List Bool → Bool)) (p y : List Bool)
    (lengths : ms.length = y.length) :
    triangular ms p (untriangular ms p y) = y := by
  induction ms generalizing p y with
  | nil => cases y <;> simp_all [triangular, untriangular]
  | cons m ms ih =>
    cases y with
    | nil => simp at lengths
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp [triangular, untriangular, mask_cancel, ih _ _ lengths]

/-- Any defect has an index, but its absence concerns the entire submitted array. -/
def lengthTag {ι : Type} (flag : Bool) (defect : ι → Prop) [Decidable (∃ i, defect i)] : Nat :=
  if flag then (if ∃ i, defect i then 2 else 0) else 1

theorem strict_threshold_has_defect_test {ι : Type} (flag : Bool) (defect : ι → Prop)
    [Decidable (∃ i, defect i)] (g c d k : Nat) (gc : g < c) (cd : c < d) :
    k < (if flag then (if ∃ i, defect i then d else g) else c) ↔
      (flag = false ∧ k < c) ∨
      (flag = true ∧ (k < g ∨ (k < d ∧ ∃ i, defect i))) := by
  cases flag <;> by_cases h : ∃ i, defect i <;> simp [h] <;> omega

theorem shortest_of_positive {R ι : Type} (defect : R → ι → Prop)
    [∀ r, Decidable (∃ i, defect r i)] (good : R) (ok : ¬ ∃ i, defect good i)
    (r : R) (flag : Bool)
    (minimal : ∀ f a, lengthTag flag (defect r) ≤ lengthTag f (defect a)) :
    flag = true ∧ ¬ ∃ i, defect r i := by
  have bound := minimal true good
  cases flag <;> by_cases h : ∃ i, defect r i <;> simp_all [lengthTag]

theorem shortest_of_negative {R ι : Type} (defect : R → ι → Prop)
    [∀ r, Decidable (∃ i, defect r i)] (bad : ∀ r, ∃ i, defect r i)
    (r : R) (flag : Bool)
    (minimal : ∀ f a, lengthTag flag (defect r) ≤ lengthTag f (defect a)) :
    flag = false := by
  have bound := minimal false r
  cases flag <;> simp_all [lengthTag]

#print axioms consistent_iff_complete
#print axioms selected_library_row
#print axioms undo_triangular
#print axioms redo_triangular
#print axioms strict_threshold_has_defect_test
#print axioms shortest_of_positive
#print axioms shortest_of_negative

end NativeBlockCompiler
