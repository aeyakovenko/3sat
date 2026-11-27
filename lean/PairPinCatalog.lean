import Std

namespace PairPinCatalog

/-- Pair responses use a single base relation and force both named bits true. -/
def pairAccepts {α : Type} (edge : α → α → Prop) (a b : α) : Prop :=
  ∃ x : α → Bool, x a = true ∧ x b = true ∧
    ∀ i j, edge i j → ¬ (x i = true ∧ x j = true)

theorem two_pins_iff_nonedge {α : Type} {edge : α → α → Prop}
    (irreflexive : ∀ i, ¬ edge i i) (symm : ∀ i j, edge i j → edge j i)
    (a b : α) : pairAccepts edge a b ↔ ¬ edge a b := by
  constructor
  · rintro ⟨x, ha, hb, ok⟩ hab
    exact ok a b hab ⟨ha, hb⟩
  · intro h
    classical
    let x : α → Bool := fun i => decide (i = a ∨ i = b)
    refine ⟨x, by simp [x], by simp [x], ?_⟩
    intro i j hij active
    have hi : i = a ∨ i = b := by simpa [x] using active.1
    have hj : j = a ∨ j = b := by simpa [x] using active.2
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact irreflexive _ hij
    · exact h hij
    · exact h (symm _ _ hij)
    · exact irreflexive _ hij

theorem induced_extension_preserves_answers {α β : Type} (embed : α → β)
    (old : α → α → Prop) (new : β → β → Prop)
    (oldIr : ∀ i, ¬ old i i) (oldSym : ∀ i j, old i j → old j i)
    (newIr : ∀ i, ¬ new i i) (newSym : ∀ i j, new i j → new j i)
    (induced : ∀ i j, old i j ↔ new (embed i) (embed j)) (a b : α) :
    pairAccepts old a b ↔ pairAccepts new (embed a) (embed b) := by
  rw [two_pins_iff_nonedge oldIr oldSym, two_pins_iff_nonedge newIr newSym]
  exact not_congr (induced a b)

/-- Between each pair of vertex groups, its incidence relation recovers the
matching exactly. Injectivity holds for arbitrary functions as well. -/
theorem matching_tags_recover {I J K : Type} {p q : I → J → K → K}
    (same : ∀ i j a b, (p i j a = b) ↔ (q i j a = b)) : p = q := by
  funext i j a
  exact ((same i j a (p i j a)).mp rfl).symm

structure Item where
  starts : Bool
  closes : Bool
  bit : Bool

structure Cursor where
  ok : Bool
  prev : Bool
  first : Bool

def step (s : Cursor) (z : Item) : Cursor :=
  let first := if z.starts then z.bit else s.first
  ⟨s.ok && !(!z.starts && s.prev && z.bit) && !(z.closes && first && z.bit),
    z.bit, first⟩

def run (s : Cursor) : List Item → Cursor
  | [] => s
  | z :: zs => run (step s z) zs

/-- Boundary flags are fixed for the input graph before the two pins are requested. -/
def emit (starts closes : Bool) : List Bool → List Item
  | [] => []
  | b :: bs => ⟨starts, bs.isEmpty && closes, b⟩ :: emit false closes bs

def adjacent (prev : Bool) : List Bool → Bool
  | [] => true
  | b :: bs => !(prev && b) && adjacent b bs

def lastSeen (prev : Bool) : List Bool → Bool
  | [] => prev
  | b :: bs => lastSeen b bs

def componentOK (closes : Bool) : List Bool → Bool
  | [] => true
  | first :: bs => adjacent first bs && !(closes && first && lastSeen first bs)

private theorem suffix_correct (closes b : Bool) (bs : List Bool) (s : Cursor) :
    (run s (emit false closes (b :: bs))).ok =
      (s.ok && adjacent s.prev (b :: bs) && !(closes && s.first && lastSeen b bs)) := by
  induction bs generalizing b s with
  | nil => simp [run, emit, step, adjacent, lastSeen]
  | cons c cs ih =>
    change (run (step s ⟨false, false, b⟩) (emit false closes (c :: cs))).ok = _
    rw [ih]
    simp [step, adjacent, lastSeen, Bool.and_assoc]

theorem component_correct (s : Cursor) (closes : Bool) (bits : List Bool) :
    (run s (emit true closes bits)).ok = (s.ok && componentOK closes bits) := by
  cases bits with
  | nil => simp [run, emit, componentOK]
  | cons b bs =>
    cases bs with
    | nil => simp [run, emit, componentOK, step, adjacent, lastSeen]
    | cons c cs =>
      change (run (step s ⟨true, false, b⟩) (emit false closes (c :: cs))).ok = _
      rw [suffix_correct]
      simp [step, componentOK, lastSeen, Bool.and_assoc]

theorem run_append (s : Cursor) (xs ys : List Item) :
    run s (xs ++ ys) = run (run s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => exact ih (step s a)

theorem components_correct (s : Cursor) (parts : List (Bool × List Bool)) :
    (run s (parts.flatMap fun p => emit true p.1 p.2)).ok =
      (s.ok && parts.all fun p => componentOK p.1 p.2) := by
  induction parts generalizing s with
  | nil => simp [run]
  | cons p ps ih =>
    simp only [List.flatMap_cons, run_append, ih, component_correct, List.all_cons,
      Bool.and_assoc]

end PairPinCatalog
