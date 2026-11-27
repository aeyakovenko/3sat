import Std

/-! Double counting behind the static cut-packing ceiling. The terminals list omits
the hub, and each cut is oriented away from the hub. Rational cut weights can be
cleared to natural multiplicities. -/
namespace CutPacking

def total (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + total rest f

private theorem total_zero (xs : List α) : total xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, ih]

private theorem total_add (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp only [total, ih]; omega

private theorem interchange (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) =
      total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp only [total, total_zero]
  | cons x xs ih => simp only [total, total_add, ih]

private theorem total_mono (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    exact Nat.add_le_add (h x (List.mem_cons_self ..))
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem total_const (xs : List α) (b : Nat) :
    total xs (fun _ => b) = xs.length * b := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_mul, Nat.add_comm]

/-- score c is bounded by the total charges of cut c. Each input terminal receives
at most budget total charge across all cuts. -/
theorem bound (cuts : List α) (terminals : List β) (score : α → Nat)
    (charge : α → β → Nat) (budget : Nat)
    (cut_bound : ∀ c ∈ cuts, score c ≤ total terminals (charge c))
    (pair_load : ∀ t ∈ terminals, total cuts (fun c => charge c t) ≤ budget) :
    total cuts score ≤ terminals.length * budget := by
  calc
    total cuts score ≤ total cuts (fun c => total terminals (charge c)) :=
      total_mono _ _ _ cut_bound
    _ = total terminals (fun t => total cuts (fun c => charge c t)) :=
      interchange cuts terminals charge
    _ ≤ total terminals (fun _ => budget) := total_mono _ _ _ pair_load
    _ = _ := total_const terminals budget

#print axioms bound
end CutPacking
