import Std

namespace PushdownDefectProbes

inductive Stage where | entry | middle | exit
  deriving DecidableEq

open Stage

variable {V : Type}

inductive Mark (x : V → Prop) (left right : V → V) : (V × Stage) → (V × Stage) → Prop
  | diag (p) : Mark x left right p p
  | first (v) (h : x (left v)) : Mark x left right (v, entry) (v, middle)
  | second (v) (h : x (right v)) : Mark x left right (v, middle) (v, exit)
  | full (v) (h : x v) : Mark x left right (v, entry) (v, exit)

inductive Push (left right : V → V) : (V × Stage) → Bool → (V × Stage) → Prop
  | first (v) : Push left right (v, entry) false (left v, entry)
  | second (v) : Push left right (v, middle) true (right v, entry)

inductive Pop (left right : V → V) : (V × Stage) → Bool → (V × Stage) → Prop
  | first (v) : Pop left right (left v, exit) false (v, middle)
  | second (v) : Pop left right (right v, exit) true (v, exit)

variable {x : V → Prop} {left right : V → V}

theorem full_iff {u v : V} :
    Mark x left right (u, entry) (v, exit) ↔ u = v ∧ x u := by
  constructor
  · intro h
    cases h with | full _ truth => exact ⟨rfl, truth⟩
  · rintro ⟨rfl, truth⟩
    exact .full _ truth

theorem wrap_closed
    (linj : ∀ u v, left u = left v → u = v)
    (rinj : ∀ u v, right u = right v → u = v)
    {a b c d : V × Stage} {tag : Bool} (push : Push left right a tag b)
    (inside : Mark x left right b c) (pop : Pop left right c tag d) :
    Mark x left right a d := by
  cases push with
  | first u =>
    cases pop with
    | first v =>
      obtain ⟨e, truth⟩ := full_iff.mp inside
      cases linj u v e
      exact .first _ truth
  | second u =>
    cases pop with
    | second v =>
      obtain ⟨e, truth⟩ := full_iff.mp inside
      cases rinj u v e
      exact .second _ truth

theorem concat_defect_iff {a b c : V × Stage} :
    (Mark x left right a b ∧ Mark x left right b c ∧ ¬Mark x left right a c) ↔
    ∃ v, a = (v, entry) ∧ b = (v, middle) ∧ c = (v, exit) ∧
      x (left v) ∧ x (right v) ∧ ¬x v := by
  constructor
  · rintro ⟨hab, hbc, missing⟩
    cases hab with
    | diag _ => exact False.elim (missing hbc)
    | first v l =>
      cases hbc with
      | diag _ => exact False.elim (missing (.first v l))
      | second _ r => exact ⟨v, rfl, rfl, rfl, l, r, fun h => missing (.full v h)⟩
    | second v r =>
      cases hbc with
      | diag _ => exact False.elim (missing (.second v r))
    | full v h =>
      cases hbc with
      | diag _ => exact False.elim (missing (.full v h))
  · rintro ⟨v, rfl, rfl, rfl, l, r, bad⟩
    exact ⟨.first v l, .second v r, fun h => bad (full_iff.mp h).2⟩

/-- The virtual true position before a line makes its first rule a fact. -/
def lineDefect (bits : Nat → Prop) (j : Nat) : Prop :=
  ¬bits j ∧ (j = 0 ∨ bits (j - 1))

theorem threshold_unique (cut j : Nat) :
    lineDefect (fun t => t < cut) j ↔ j = cut := by
  unfold lineDefect
  omega

end PushdownDefectProbes
