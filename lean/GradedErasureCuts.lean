import Std

namespace GradedErasureCuts

private def total {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: tail => f x + total tail f

private theorem total_add {α : Type} (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [total, ih]; omega

private theorem total_zero {α : Type} (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs <;> simp_all [total]

private theorem total_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) = total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => exact (total_zero ys).symm
  | cons x xs ih => simp only [total, total_add, ih]

private theorem total_const {α : Type} (xs : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ xs, f x = c) : total xs f = xs.length * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have head := h x List.mem_cons_self
    have tail := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [total, head, tail, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem total_bounded {α : Type} (xs : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ xs, f x ≤ c) : total xs f ≤ xs.length * c := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    have head := h x List.mem_cons_self
    have tail := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [total, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Count only incidences from a chosen left subfamily to its neighbors. Every
left vertex has full degree, while only an upper bound holds on the right. -/
theorem hall_neighborhood {α β : Type} (left : List α) (neighbors : List β)
    (edges : α → β → Nat) (leftDegree rightDegree : Nat)
    (positive : 0 < rightDegree) (more : rightDegree ≤ leftDegree)
    (full : ∀ a ∈ left, total neighbors (edges a) = leftDegree)
    (bounded : ∀ b ∈ neighbors, total left (fun a => edges a b) ≤ rightDegree) :
    left.length ≤ neighbors.length := by
  have bound : left.length * rightDegree ≤ neighbors.length * rightDegree := by
    calc
      left.length * rightDegree ≤ left.length * leftDegree := Nat.mul_le_mul_left _ more
      _ = total left (fun a => total neighbors (edges a)) := (total_const _ _ _ full).symm
      _ = total neighbors (fun b => total left (fun a => edges a b)) := total_swap _ _ _
      _ ≤ neighbors.length * rightDegree := total_bounded _ _ _ bounded
  exact Nat.le_of_mul_le_mul_right bound positive

/-- A frozen-prefix equality bit plus a prediction using only the holes suffices
for any completion, provided the chosen public prediction fits the database there. -/
theorem suffix_prediction {ι Symbol : Type} (hole : ι → Bool) (a x prediction : ι → Symbol)
    (fits : ∀ i, hole i = true → prediction i = a i) :
    ((∀ i, hole i = false → x i = a i) ∧ (∀ i, hole i = true → x i = prediction i)) ↔
      (∀ i, x i = a i) := by
  constructor
  · rintro ⟨outside, inside⟩ i
    cases hi : hole i with
    | false => exact outside i hi
    | true => exact (inside i hi).trans (fits i hi)
  · intro equal
    exact ⟨fun i _ => equal i, fun i hi => (equal i).trans (fits i hi).symm⟩

end GradedErasureCuts

#print axioms GradedErasureCuts.hall_neighborhood
#print axioms GradedErasureCuts.suffix_prediction
