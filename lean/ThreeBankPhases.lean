import Std

namespace ThreeBankPhases

/-- If all three banks are first used, the last requester has seen both others. -/
theorem last_first_access (x y z : Nat) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    (y < x ∧ z < x) ∨ (x < y ∧ z < y) ∨ (x < z ∧ y < z) := by
  omega

/-- If no party can see both earlier first uses, at least one bank is untouched.
    Missing times use a sentinel equal to the horizon. -/
theorem unseen_bank (x y z horizon : Nat)
    (hx : x ≤ horizon) (hy : y ≤ horizon) (hz : z ≤ horizon)
    (hxy : x = y → x = horizon) (hxz : x = z → x = horizon)
    (hyz : y = z → y = horizon)
    (px : x < horizon → ¬ (y < x ∧ z < x))
    (py : y < horizon → ¬ (x < y ∧ z < y))
    (pz : z < horizon → ¬ (x < z ∧ y < z)) :
    x = horizon ∨ y = horizon ∨ z = horizon := by
  omega

/-- Flipping one sign label pairs the terms of a mismatched equality. -/
def flipSign {α : Type} [DecidableEq α] (a : α) (f : α → Bool) (i : α) :=
  if i = a then !(f i) else f i

theorem flip_is_involution {α : Type} [DecidableEq α] (a : α) (f : α → Bool) :
    flipSign a (flipSign a f) = f := by
  funext i
  by_cases h : i = a <;> simp [flipSign, h]

theorem flip_mismatch {α : Type} [DecidableEq α] (a b : α) (h : b ≠ a)
    (f : α → Bool) :
    (flipSign a f a == flipSign a f b) = !(f a == f b) := by
  simp only [flipSign, if_pos rfl, if_neg h]
  cases f a <;> cases f b <;> decide

/-- The parity of marked endpoints of a list of certified path fragments. -/
def markedEnds {α : Type} (mark : α → Bool) : List (α × α) → Bool
  | [] => false
  | (a, b) :: rest => (mark a ^^ mark b) ^^ markedEnds mark rest

theorem markedEnds_false {α : Type} (mark : α → Bool) (edges : List (α × α))
    (stable : ∀ p ∈ edges, mark p.1 = mark p.2) : markedEnds mark edges = false := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨a, b⟩
    have h : mark a = mark b := stable (a, b) (by simp)
    have rest : ∀ p ∈ es, mark p.1 = mark p.2 := by
      intro p hp
      exact stable p (by simp [hp])
    simp [markedEnds, h, ih rest]

theorem basin_agreement {α : Type} (mark : α → Bool) (edges : List (α × α))
    (a b : α) (stable : ∀ p ∈ edges, mark p.1 = mark p.2)
    (syndrome : markedEnds mark edges = (mark a ^^ mark b)) : mark a = mark b := by
  rw [markedEnds_false mark edges stable] at syndrome
  cases ha : mark a <;> cases hb : mark b <;> simp_all

def advance {α : Type} (f : α → α) : Nat → α → α
  | 0, s => s
  | n + 1, s => f (advance f n s)

theorem advance_add {α : Type} (f : α → α) (s : α) (n k : Nat) :
    advance f (n + k) s = advance f k (advance f n s) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [advance, Nat.add_succ, ih]

/-- A deterministic orbit cannot repeat a state before its first halt. -/
theorem distinct_before_halt {α : Type} (f : α → α) (s : α) (halts : α → Prop)
    (a b stop : Nat) (hab : a < b) (hbs : b ≤ stop)
    (atStop : halts (advance f stop s))
    (first : ∀ t < stop, ¬ halts (advance f t s)) :
    advance f a s ≠ advance f b s := by
  intro eq
  have later : advance f (a + (stop - b)) s = advance f (b + (stop - b)) s := by
    rw [advance_add, advance_add, eq]
  have right : b + (stop - b) = stop := by omega
  rw [right] at later
  exact first _ (by omega : a + (stop - b) < stop) (later.symm ▸ atStop)

end ThreeBankPhases
