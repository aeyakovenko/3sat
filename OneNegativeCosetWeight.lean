import Std

namespace OneNegativeCosetWeight

structure CubicRows (α : Type) where
  labels : List α
  p : α → α
  q : α → α
  pPerm : (labels.map p).Perm labels
  qPerm : (labels.map q).Perm labels

namespace CubicRows

variable {α : Type}

def total (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

private theorem total_perm {xs ys : List α} (h : xs.Perm ys) (f : α → Nat) :
    total xs f = total ys f := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [total, List.map_cons, List.sum_cons] at *; omega
  | swap => simp only [total, List.map_cons, List.sum_cons]; omega
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem total_three (xs : List α) (f g h : α → Nat) :
    total xs (fun v => f v + g v + h v) = total xs f + total xs g + total xs h := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total, List.map_cons, List.sum_cons] at *; omega

def row (a : CubicRows α) (f : α → Nat) (u : α) := f u + f (a.p u) + f (a.q u)

private theorem column_total (a : CubicRows α) (f : α → Nat) :
    total a.labels (a.row f) = 3 * total a.labels f := by
  have hp := total_perm a.pPerm f
  have hq := total_perm a.qPerm f
  simp only [total, List.map_map, Function.comp_def] at hp hq
  unfold row
  rw [total_three]
  unfold total
  omega

private theorem total_one_twice (xs : List α) (f g : α → Nat)
    (h : ∀ u ∈ xs, f u = 1 + 2 * g u) :
    total xs f = xs.length + 2 * total xs g := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
    have hu := h u (by simp)
    have ht := ih (fun v hv => h v (by simp [hv]))
    simp only [total, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

private theorem total_zero_iff (xs : List α) (f : α → Nat) :
    total xs f = 0 ↔ ∀ u ∈ xs, f u = 0 := by
  induction xs with
  | nil => simp [total]
  | cons u xs ih =>
    change f u + total xs f = 0 ↔ _
    rw [Nat.add_eq_zero_iff, ih]
    simp

def weight (a : CubicRows α) (x : α → Bool) := total a.labels (fun i => (x i).toNat)

def load (a : CubicRows α) (x : α → Bool) := a.row (fun i => (x i).toNat)

def OddWord (a : CubicRows α) (x : α → Bool) :=
  ∀ u ∈ a.labels, a.load x u = 1 ∨ a.load x u = 3

def Cover (a : CubicRows α) (x : α → Bool) :=
  ∀ u ∈ a.labels, a.load x u = 1

/-- Every odd word has exact-cover weight or exceeds it by at least two. -/
theorem gap_two (a : CubicRows α) {k : Nat} (size : a.labels.length = 3*k)
    (x : α → Bool) (odd : a.OddWord x) :
    (a.weight x = k ↔ a.Cover x) ∧ (a.weight x = k ∨ k+2 ≤ a.weight x) := by
  let bad := fun u => if a.load x u = 3 then 1 else 0
  have localCount : ∀ u ∈ a.labels, a.load x u = 1 + 2 * bad u := by
    intro u hu
    rcases odd u hu with h|h <;> simp [bad,h]
  have count := total_one_twice a.labels (a.load x) bad localCount
  have ct : total a.labels (a.load x) = 3 * a.weight x := column_total _ _
  have full : a.Cover x ↔ total a.labels bad = 0 := by
    rw [total_zero_iff]
    constructor
    · intro cov u hu
      simp [bad, cov u hu]
    · intro h u hu
      have hh := localCount u hu
      rw [h u hu] at hh
      omega
  constructor
  · rw [full]
    omega
  · omega

inductive Entry | neg | zero | one deriving DecidableEq

def Entry.value : Entry → Int | .neg => -1 | .zero => 0 | .one => 1
def Entry.bit : Entry → Bool | .neg => true | .zero => false | .one => true
def Entry.negative : Entry → Nat | .neg => 1 | .zero => 0 | .one => 0

private theorem reduce_row (a b c : Entry) (h : a.value+b.value+c.value=1) :
    (a.bit.toNat+b.bit.toNat+c.bit.toNat = 1 ∨ a.bit.toNat+b.bit.toNat+c.bit.toNat=3) ∧
    a.bit.toNat+b.bit.toNat+c.bit.toNat=1+2*(a.negative+b.negative+c.negative) := by
  cases a <;> cases b <;> cases c <;> revert h <;> decide

/-- Reducing the given signed solution modulo two supplies an odd word precisely
two above the lowest possible weight. Together with gap_two this determines
the minimum weight in the all-odd syndrome coset in both verdicts. -/
theorem supplied_word (a : CubicRows α) {k : Nat} (size : a.labels.length=3*k)
    (y : α → Entry) (oneNeg : total a.labels (fun i => (y i).negative) = 1)
    (signed : ∀ u ∈ a.labels, (y u).value + (y (a.p u)).value + (y (a.q u)).value = 1) :
    let x := fun i => (y i).bit
    a.OddWord x ∧ a.weight x = k+2 := by
  let x := fun i => (y i).bit
  let neg := fun i => (y i).negative
  have leg (u) (hu : u ∈ a.labels) := reduce_row _ _ _ (signed u hu)
  have odd : a.OddWord x := fun u hu => (leg u hu).1
  have count := total_one_twice a.labels (a.load x) (a.row neg) (fun u hu => (leg u hu).2)
  have nct := column_total a neg
  have ct : total a.labels (a.load x) = 3*a.weight x := column_total _ _
  have one : total a.labels neg = 1 := oneNeg
  change a.OddWord x ∧ a.weight x = k+2
  exact ⟨odd, by omega⟩

end CubicRows

end OneNegativeCosetWeight
