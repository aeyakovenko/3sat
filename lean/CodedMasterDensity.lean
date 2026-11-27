import Std

namespace CodedMasterDensity

variable {Input Trial Program Row Output Old Fresh : Type}

def mass {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + mass rest f

private theorem mass_zero {α : Type} (xs : List α) :
    mass xs (fun _ => 0) = 0 := by induction xs <;> simp [mass, *]

private theorem mass_const {α : Type} (xs : List α) (c : Nat) :
    mass xs (fun _ => c) = xs.length * c := by
  induction xs with
  | nil => simp [mass]
  | cons x tail ih => simp [mass, ih, Nat.succ_mul, Nat.add_comm]

private theorem mass_add {α : Type} (xs : List α) (f g : α → Nat) :
    mass xs (fun x => f x + g x) = mass xs f + mass xs g := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [mass, ih]; omega

private theorem mass_mono {α : Type} (xs : List α) {f g : α → Nat}
    (h : ∀ x ∈ xs, f x ≤ g x) : mass xs f ≤ mass xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x tail ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem term_le_mass {α : Type} (xs : List α) (f : α → Nat) {x : α}
    (hx : x ∈ xs) : f x ≤ mass xs f := by
  induction xs with
  | nil => simp at hx
  | cons y tail ih =>
    rcases List.mem_cons.mp hx with rfl | rest
    · simp [mass]
    · exact Nat.le_trans (ih rest) (Nat.le_add_left _ _)

/-- Double counting with arbitrary nonnegative integral incidence weights. -/
theorem sum_by_trials (inputs : List Input) (trials : List Trial)
    (inc : Input → Trial → Nat) :
    mass inputs (fun x => mass trials (inc x)) =
    mass trials (fun u => mass inputs (fun x => inc x u)) := by
  induction inputs with
  | nil => simp only [mass]; exact (mass_zero trials).symm
  | cons x xs ih => simp only [mass, ih, mass_add]

/-- The number of exceptional inputs times their guaranteed witness count
is at most the number of trials times the per-trial exception cap. -/
theorem incidence_bound (exceptions : List Input) (trials : List Trial)
    (inc : Input → Trial → Nat) (a b : Nat)
    (row : ∀ x ∈ exceptions, a ≤ mass trials (inc x))
    (col : ∀ u ∈ trials, mass exceptions (fun x => inc x u) ≤ b) :
    exceptions.length * a ≤ trials.length * b := by
  calc
    exceptions.length * a = mass exceptions (fun _ => a) := (mass_const _ _).symm
    _ ≤ mass exceptions (fun x => mass trials (inc x)) := mass_mono _ row
    _ = mass trials (fun u => mass exceptions (fun x => inc x u)) := sum_by_trials _ _ _
    _ ≤ mass trials (fun _ => b) := mass_mono _ col
    _ = trials.length * b := mass_const _ _

/-- For a portfolio with different trial populations and caps, a prescribed
fiber strictly larger than the total exception budget has a common survivor.
All lists count occurrences. Use duplicate-free lists for set cardinalities. -/
theorem common_survivor (fiber : List Input) (programs : List Program)
    (trials : Program → List Trial) (bad : Program → Input → Bool)
    (inc : Program → Input → Trial → Nat) (a : Nat) (b : Program → Nat)
    (row : ∀ p ∈ programs, ∀ x ∈ fiber, bad p x = true → a ≤ mass (trials p) (inc p x))
    (col : ∀ p ∈ programs, ∀ u ∈ trials p,
      mass fiber (fun x => if bad p x then inc p x u else 0) ≤ b p)
    (budget : mass programs (fun p => (trials p).length * b p) < fiber.length * a) :
    ∃ x ∈ fiber, ∀ p ∈ programs, bad p x = false := by
  classical
  have per (p : Program) (hp : p ∈ programs) :
      mass fiber (fun x => if bad p x then a else 0) ≤ (trials p).length * b p := by
    calc
      _ ≤ mass fiber (fun x => mass (trials p) (fun u => if bad p x then inc p x u else 0)) := by
        apply mass_mono
        intro x hx
        cases h : bad p x with
        | false => simp [h]
        | true => simpa [h] using row p hp x hx h
      _ = mass (trials p) (fun u => mass fiber (fun x => if bad p x then inc p x u else 0)) :=
        sum_by_trials _ _ _
      _ ≤ mass (trials p) (fun _ => b p) := mass_mono _ (col p hp)
      _ = _ := mass_const _ _
  apply Classical.byContradiction
  intro none
  have covers (x : Input) (hx : x ∈ fiber) : ∃ p ∈ programs, bad p x = true := by
    apply Classical.byContradiction
    intro missing
    apply none
    refine ⟨x, hx, fun p hp => ?_⟩
    cases h : bad p x with
    | false => rfl
    | true => exact False.elim (missing ⟨p, hp, h⟩)
  have total : fiber.length * a ≤ mass programs (fun p => (trials p).length * b p) := by
    calc
      _ = mass fiber (fun _ => a) := (mass_const _ _).symm
      _ ≤ mass fiber (fun x => mass programs (fun p => if bad p x then a else 0)) := by
        apply mass_mono
        intro x hx
        obtain ⟨p, hp, hit⟩ := covers x hx
        simpa [hit] using term_le_mass programs (fun j => if bad j x then a else 0) hp
      _ = mass programs (fun p => mass fiber (fun x => if bad p x then a else 0)) :=
        sum_by_trials _ _ _
      _ ≤ _ := mass_mono _ per
  exact (Nat.not_lt_of_ge total) budget

/-- Keep the entire old row and its prescribed output rectangle. Surjectivity
of the linear map on the fresh columns supplies a correction for each row
independently. Only pointwise XOR and the stated surjectivity are needed. -/
theorem lift_output_rectangle (oldRows : Row → Old) (desired : Row → Output → Bool)
    (oldPart : Old → Output → Bool) (freshPart : Fresh → Output → Bool)
    (onto : ∀ v : Output → Bool, ∃ w, freshPart w = v) :
    ∃ extended : Row → Old × Fresh, (∀ i, (extended i).1 = oldRows i) ∧
      ∀ i j, (oldPart (extended i).1 j ^^ freshPart (extended i).2 j) = desired i j := by
  classical
  let correction (i : Row) := fun j => oldPart (oldRows i) j ^^ desired i j
  refine ⟨fun i => (oldRows i, Classical.choose (onto (correction i))), fun _ => rfl, ?_⟩
  intro i j
  have shift := congrFun (Classical.choose_spec (onto (correction i))) j
  simp only at *
  rw [shift]
  cases hp : oldPart (oldRows i) j <;> simp [correction, hp]

end CodedMasterDensity
