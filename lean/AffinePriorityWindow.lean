import Std

namespace AffinePriorityWindow

abbrev State := Nat → Bool

structure Row where
  pivot : Nat
  prior : List Nat
  early : ∀ i ∈ prior, i < pivot
  rhs : Bool

def parity (x : State) : List Nat → Bool
  | [] => false
  | i :: is => x i ^^ parity x is

private theorem parity_congr (x y : State) (is : List Nat)
    (same : ∀ i ∈ is, x i = y i) : parity x is = parity y is := by
  induction is with
  | nil => rfl
  | cons head tail ih =>
    simp only [parity]
    rw [same head (by simp), ih (fun i hi => same i (by simp [hi]))]

def satisfies (x : State) (row : Row) : Prop :=
  (x row.pivot ^^ parity x row.prior) = row.rhs

def applyRow (x : State) (row : Row) : State := fun i =>
  if i = row.pivot then row.rhs ^^ parity x row.prior else x i

theorem respects_row (x : State) (row : Row) : satisfies (applyRow x row) row := by
  have prev : parity (applyRow x row) row.prior = parity x row.prior :=
    parity_congr _ _ _ (fun i hi => by
      have ne := Nat.ne_of_lt (row.early i hi)
      simp [applyRow, ne])
  unfold satisfies
  rw [prev]
  simp [applyRow]

theorem unchanged_below (x : State) (row : Row) (i : Nat) (h : i < row.pivot) :
    applyRow x row i = x i := by simp [applyRow, Nat.ne_of_lt h]

def applyRows (x : State) : List Row → State
  | [] => x
  | r :: rs => applyRows (applyRow x r) rs

theorem untouched (x : State) (rs : List Row) (i : Nat)
    (early : ∀ r ∈ rs, i < r.pivot) : applyRows x rs i = x i := by
  induction rs generalizing x with
  | nil => rfl
  | cons head tail ih =>
    have ht : ∀ r ∈ tail, i < r.pivot := fun r h => early r (by simp [h])
    exact (ih (applyRow x head) ht).trans (unchanged_below _ _ _ (early head (by simp)))

theorem realize (x : State) (rs : List Row)
    (ordered : rs.Pairwise (fun a b => a.pivot < b.pivot)) :
    ∀ r ∈ rs, satisfies (applyRows x rs) r := by
  induction rs generalizing x with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨before, remaining⟩ := List.pairwise_cons.mp ordered
    intro r hr
    rcases List.mem_cons.mp hr with eq | htail
    · subst r
      change satisfies (applyRows (applyRow x head) tail) head
      unfold satisfies
      rw [untouched _ _ _ before]
      rw [parity_congr _ (applyRow x head) head.prior
        (fun i hi => untouched _ _ _ (fun r hr => Nat.lt_trans (head.early i hi) (before r hr)))]
      exact respects_row x head
    · exact ih (applyRow x head) remaining r htail

def startsBelow (s : Nat → Nat) : Nat → Nat
  | 0 => 0
  | e+1 => startsBelow s e + s e

/-- Every failed start is interrupted by a new higher-priority start. -/
theorem start_budget (starts : Nat → Nat)
    (charged : ∀ e, starts e ≤ startsBelow starts e + 1) :
    ∀ e, startsBelow starts e + 1 ≤ 2^e := by
  intro e
  induction e with
  | zero => simp [startsBelow]
  | succ e ih =>
    have he := charged e
    simp only [startsBelow, Nat.pow_succ]
    omega

theorem rank_starts (s : Nat → Nat) (h : ∀ e, s e ≤ startsBelow s e + 1) (e : Nat) :
    s e ≤ 2^e := Nat.le_trans (h e) (start_budget s h e)

end AffinePriorityWindow
