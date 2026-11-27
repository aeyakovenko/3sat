import Std

namespace AffineReservoirUpdate

/-- A coefficient is given by its variables of odd incidence. Repeated
    occurrences are permitted, so concatenation implements row addition. -/
def parity {I : Type} (v : I → Bool) : List I → Bool
  | [] => false
  | i :: rest => v i ^^ parity v rest

theorem parity_append {I : Type} (v : I → Bool) (xs ys : List I) :
    parity v (xs ++ ys) = (parity v xs ^^ parity v ys) := by
  induction xs with
  | nil => simp [parity]
  | cons i xs ih => simp [parity, ih, Bool.xor_assoc]

structure Row (I : Type) where
  constant : Bool
  indices : List I

def eval {I : Type} (r : Row I) (v : I → Bool) := r.constant ^^ parity v r.indices

def add {I : Type} (r s : Row I) : Row I :=
  ⟨r.constant ^^ s.constant, r.indices ++ s.indices⟩

theorem eval_add {I : Type} (r s : Row I) (v : I → Bool) :
    eval (add r s) v = (eval r v ^^ eval s v) := by
  simp only [eval, add, parity_append]
  cases r.constant <;> cases s.constant <;> cases parity v r.indices <;>
    cases parity v s.indices <;> decide

/-- Split off the distinguished (retiring) coordinate from the other free bits. -/
structure WithPivot (I : Type) where
  coefficient : Bool
  rest : Row I

def before {I : Type} (r : WithPivot I) (p : Bool) (v : I → Bool) :=
  eval r.rest v ^^ (r.coefficient && p)

def substitute {I : Type} (r : WithPivot I) (pivotValue : Row I) :=
  if r.coefficient then add r.rest pivotValue else r.rest

theorem eval_substitute {I : Type} (r : WithPivot I) (f : Row I) (v : I → Bool) :
    eval (substitute r f) v = before r (eval f v) v := by
  cases r with
  | mk c s => cases c <;> simp [substitute, before, eval_add]

/-- The query p XOR q = side uniquely determines p. -/
def solved {I : Type} (q : Row I) (side : Bool) : Row I :=
  ⟨side ^^ q.constant, q.indices⟩

theorem solve_iff {I : Type} (q : Row I) (side p : Bool) (v : I → Bool) :
    ((p ^^ eval q v) = side) ↔ p = eval (solved q side) v := by
  cases q with
  | mk c xs =>
    simp only [solved, eval]
    cases p <;> cases side <;> cases c <;> cases parity v xs <;> decide

/-- Equality of full relations after a reservoir swap, for arbitrary old
    expressed originals and arbitrary source predicate. The untouched bit x
    occupies the retiring coordinate's slot and remains independent. -/
theorem swap_image {I J : Type} (old : J → WithPivot I) (q : Row I) (side : Bool)
    (allowed : (J → Bool) → Bool → Bool → (I → Bool) → Prop) :
    (∃ v p x, (p ^^ eval q v) = side ∧ allowed (fun j => before (old j) p v) p x v) ↔
    (∃ v x, allowed (fun j => eval (substitute (old j) (solved q side)) v)
                    (eval (solved q side) v) x v) := by
  simp only [eval_substitute, solve_iff]
  constructor
  · rintro ⟨v, p, x, hp, h⟩
    subst p
    exact ⟨v, x, h⟩
  · rintro ⟨v, x, h⟩
    exact ⟨v, _, x, rfl, h⟩

/-- When the equation uses the fresh bit, previous rows are unchanged and
    the fresh bit acquires its single affine expression. -/
theorem fresh_image {I : Type} (q : Row I) (side : Bool)
    (allowed : (I → Bool) → Bool → Prop) :
    (∃ v x, (x ^^ eval q v) = side ∧ allowed v x) ↔
    (∃ v, allowed v (eval (solved q side) v)) := by
  simp only [solve_iff]
  constructor
  · rintro ⟨v, x, h, hx⟩
    exact ⟨v, h ▸ hx⟩
  · rintro ⟨v, h⟩
    exact ⟨v, _, rfl, h⟩

theorem timely_answer_preserves {A : Type} (ok : A → Prop) (test : A → Bool)
    (side reply : Bool) (parent : ∃ a, ok a)
    (sound : reply = true ↔ ∃ a, ok a ∧ test a = side) :
    ∃ a, ok a ∧ test a = (if reply then side else !side) := by
  cases reply with
  | true => exact sound.mp rfl
  | false =>
    obtain ⟨a, ha⟩ := parent
    have hne : test a ≠ side := fun h => Bool.noConfusion (sound.mpr ⟨a, ha, h⟩)
    exact ⟨a, ha, by cases side <;> cases h : test a <;> simp_all⟩

end AffineReservoirUpdate
