import Std

namespace BlindStoreAffineCuts

/-- Answers to the independent equations, in the order used by the guard. -/
def patterns : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (patterns n).map (false :: ·) ++ (patterns n).map (true :: ·)

def observed : List Bool → List Bool
  | [] => []
  | false :: _ => [false]
  | true :: xs => true :: observed xs

def cost (x : List Bool) := (observed x).length

def total {A : Type} (f : A → Nat) : List A → Nat
  | [] => 0
  | x :: xs => f x + total f xs

private theorem total_append {A : Type} (f : A → Nat) (xs ys : List A) :
    total f (xs ++ ys) = total f xs + total f ys := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_assoc]

private theorem total_false (xs : List (List Bool)) :
    total cost (xs.map (false :: ·)) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, cost, observed] at ih ⊢; omega

private theorem total_true (xs : List (List Bool)) :
    total cost (xs.map (true :: ·)) = xs.length + total cost xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, cost, observed] at ih ⊢; omega

theorem pattern_count (n : Nat) : (patterns n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [patterns, ih, Nat.pow_succ]; omega

/-- Dividing by the 2^r equally likely patterns gives 2(1-2^(-r)). -/
theorem uniform_total_cost (r : Nat) : total cost (patterns r) = 2 * (2^r - 1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [patterns, total_append, total_false, total_true, pattern_count, ih, Nat.pow_succ]
    have positive : 0 < 2^r := Nat.pow_pos (by decide)
    omega

theorem observed_preserves_guard (xs : List Bool) :
    (observed xs).all id = xs.all id := by
  induction xs with
  | nil => rfl
  | cons bit xs ih => cases bit <;> simp [observed, ih]

theorem partition_cell_has_one_verdict {x y : List Bool} (same : observed x = observed y) :
    x.all id = y.all id := by
  rw [← observed_preserves_guard x, same, observed_preserves_guard]

def guard {X : Type} (rows : List (X → Bool)) (x : X) : Bool := rows.all (fun row => row x)

/-- At a prescribed point missing the equality fiber, one failed equation
    supplies a slice through it on which the entire guard continues to miss. -/
theorem chosen_pin_miss {X : Type} (rows : List (X → Bool)) (x : X)
    (miss : guard rows x = false) :
    ∃ row ∈ rows, row x = false ∧ ∀ y, row y = false → guard rows y = false := by
  have existsBad : ∃ row ∈ rows, row x = false := by
    apply Classical.byContradiction
    intro h
    have allTrue : guard rows x = true := by
      apply List.all_eq_true.mpr
      intro row member
      cases value : row x with
      | false => exact False.elim (h ⟨row, member, value⟩)
      | true => rfl
    simp [miss] at allTrue
  obtain ⟨row, member, bad⟩ := existsBad
  refine ⟨row, member, bad, ?_⟩
  intro y fails
  cases hy : guard rows y with
  | false => rfl
  | true =>
    have good := (List.all_eq_true.mp hy) row member
    simp [fails] at good

structure Store (X V : Type) where
  hit : X → Bool
  payload : X → V

/-- Memory restricted to the one address being queried; addresses may move with x. -/
def afterStores {X V : Type} (old : X → V) (rows : List (Store X V)) (x : X) : V :=
  match rows with
  | [] => old x
  | row :: rest =>
    afterStores (fun y => if row.hit y then row.payload y else old y) rest x

/-- Later aliasing stores are harmless when they preserve the relevant value. -/
theorem harmless_tail {X V : Type} (rows : List (Store X V)) (x : X) (v : V)
    (old : X → V) (initial : old x = v)
    (preserve : ∀ row ∈ rows, row.hit x = true → row.payload x = v) :
    afterStores old rows x = v := by
  induction rows generalizing old with
  | nil => exact initial
  | cons row rest ih =>
    apply ih
    · cases h : row.hit x with
      | false => simpa [h] using initial
      | true => simpa [h] using preserve row (by simp) h
    · intro s member
      exact preserve s (by simp [member])

theorem equal_to_last_payload_on_fiber {X V : Type} (fiber : X → Prop)
    (old : X → V) (candidate : Store X V) (later : List (Store X V))
    (hit : ∀ x, fiber x → candidate.hit x = true)
    (preserve : ∀ x, fiber x → ∀ row ∈ later, row.hit x = true →
      row.payload x = candidate.payload x) :
    ∀ x, fiber x → afterStores old (candidate :: later) x = candidate.payload x := by
  intro x member
  change afterStores (fun y => if candidate.hit y then candidate.payload y else old y)
    later x = candidate.payload x
  apply harmless_tail
  · simp [hit x member]
  · exact preserve x member

theorem constant_last_feasible_store {X V : Type} (fiber : X → Prop)
    (old : X → V) (candidate : Store X V) (later : List (Store X V)) (v : V)
    (hit : ∀ x, fiber x → candidate.hit x = true)
    (payload : ∀ x, fiber x → candidate.payload x = v)
    (miss : ∀ x, fiber x → ∀ row ∈ later, row.hit x = false) :
    ∀ x, fiber x → afterStores old (candidate :: later) x = v := by
  intro x member
  apply Eq.trans _ (payload x member)
  apply equal_to_last_payload_on_fiber fiber old candidate later hit _ x member
  intro y feasible row inLater yes
  simp [miss y feasible row inLater] at yes

end BlindStoreAffineCuts
