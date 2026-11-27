import Std

namespace SingleForkAdvice

/-- False is expert zero. Expert one supplies an unconditional fallback. -/
def actual (firstAccepts : Bool) : Bool :=
  if firstAccepts then false else true

def openRow (firstAccepts row : Bool) : Prop :=
  row = true ∨ firstAccepts = true

/-- The repeatedly selected expert incurs one loss on each of the m blocks. -/
def loss (m : Nat) (selected expert : Bool) : Nat :=
  if selected = expert then m else 0

def better (m : Nat) (selected : Bool) : Bool :=
  decide (loss m selected true < loss m selected false)

theorem better_zero_iff (a : Bool) (m : Nat) (positive : 0 < m) :
    better m (actual a) = false ↔ a = false := by
  cases a <;> simp [better, loss, actual, positive]

/-- On a sound accepting claim for zero, every witnessed row is the fallback,
    which is the actual choice and makes expert zero strictly better. -/
theorem sound_zero_prediction {a : Bool} {m : Nat} (positive : 0 < m)
    {accepted : Prop} (sound : accepted → better m (actual a) = false)
    (proof : accepted) :
    a = false ∧ (∀ row, openRow a row ↔ row = true) ∧ actual a = true ∧
      loss m (actual a) false < loss m (actual a) true := by
  have ha := (better_zero_iff a m positive).mp (sound proof)
  subst a
  simp [openRow, actual, loss, positive]

/-- A complete positive proof system for the zero bit on this fork gives
    positive certificates for the complement of the first row's predicate. -/
theorem zero_certificates_refute_row {Branch Certificate : Type}
    (first : Branch → Prop) (predictsZero : Certificate → Prop) {a : Bool} {m : Nat}
    (positive : 0 < m) (row : a = true ↔ ∃ w, first w)
    (exactBit : (∃ c, predictsZero c) ↔ better m (actual a) = false) :
    (∃ c, predictsZero c) ↔ ¬∃ w, first w := by
  rw [exactBit, better_zero_iff a m positive, ← row]
  cases a <;> decide

/-- Both rows have positive witnesses in the yes-case. The fallback alone
    can then yield the opposite hindsight bit from the actual priority row. -/
theorem opposite_witnessed_bits (m : Nat) (positive : 0 < m) :
    openRow true false ∧ openRow true true ∧
      better m true ≠ better m (actual true) := by
  simp [openRow, actual, better, loss, positive]

/-- A positive witness per row fixes a finite length while allowing several
    accepting branches, several rows, and history-dependent next states. -/
inductive Path {State Row Witness : Type} (checks : State → Row → Witness → State → Prop) :
    Nat → State → List Row → State → Prop where
  | nil (s : State) : Path checks 0 s [] s
  | cons {s t u : State} {r : Row} {w : Witness} {rs : List Row} {n : Nat}
      (head : checks s r w t) (tail : Path checks n t rs u) :
      Path checks (n + 1) s (r :: rs) u

/-- On an input whose actual path has positive witnesses, guessing any
    witnessed path gives complementary bit certificates exactly when all
    such paths agree on the bit. They may disagree on their rows or states. -/
theorem witness_path_criterion {State Row Witness : Type}
    {checks : State → Row → Witness → State → Prop} {n : Nat} {start last : State}
    {actualRows : List Row} (real : Path checks n start actualRows last)
    (bit : List Row → State → Bool) :
    (∀ b, (∃ rs t, Path checks n start rs t ∧ bit rs t = b) ↔
      bit actualRows last = b) ↔
    (∀ rs t, Path checks n start rs t → bit rs t = bit actualRows last) := by
  constructor
  · intro exactBit rs t path
    exact ((exactBit _).mp ⟨rs, t, path, rfl⟩).symm
  · intro agree b
    constructor
    · rintro ⟨rs, t, path, output⟩
      exact (agree rs t path).symm.trans output
    · intro output
      exact ⟨actualRows, last, real, output⟩

private def countMarks {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countMarks p xs

private theorem marks_le {α : Type} (xs : List α) (p q : α → Bool)
    (sub : ∀ x ∈ xs, p x = true → q x = true) :
    countMarks p xs ≤ countMarks q xs := by
  induction xs with
  | nil => simp [countMarks]
  | cons x xs ih =>
    have tail := ih (fun y hy => sub y (by simp [hy]))
    have head := sub x (by simp)
    cases hp : p x <;> cases hq : q x <;> simp_all [countMarks] <;> omega

/-- If the public count of accepted names is exact, a marked subset of
    that size gives the entire menu. Use each name once in the public list
    to count distinct names, independently of the number of branch witnesses. -/
theorem known_multiplicity {α : Type} (xs : List α) (p q : α → Bool)
    (sub : ∀ x ∈ xs, p x = true → q x = true)
    (same : xs.countP p = xs.countP q) : ∀ x ∈ xs, p x = q x := by
  have counts (f : α → Bool) (ys : List α) : ys.countP f = countMarks f ys := by
    induction ys with
    | nil => simp [countMarks]
    | cons y ys ih =>
      cases hy : f y <;> simp [List.countP_cons, countMarks, hy, ih, Nat.add_comm]
  rw [counts, counts] at same
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have tailSub (y) (hy : y ∈ xs) := sub y (by simp [hy])
    have tailLe := marks_le xs p q tailSub
    have head := sub x (by simp)
    have equalHead : p x = q x := by
      cases hp : p x <;> cases hq : q x <;> simp_all [countMarks] <;> omega
    have equalTail : countMarks p xs = countMarks q xs := by
      simpa [countMarks, equalHead] using same
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · simpa [h] using equalHead
    · exact ih tailSub equalTail y h

end SingleForkAdvice
