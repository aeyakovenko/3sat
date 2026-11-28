import Std

namespace OneBitFromPropagatedSat

private def clause (u v w : Bool) : Bool := u || v || w

/-- Six shared anchor rows, the one edited row, and the four complement clauses. -/
def anchors (edited a b c p : Bool) : Bool :=
  clause a b (!c) && clause a (!b) c && clause a (!b) (!c) &&
  clause (!a) b (!c) && clause (!a) (!b) c && clause (!a) (!b) (!c) &&
  clause (!(if edited then p else a)) b c &&
  clause a p b && clause a p (!b) && clause (!a) (!p) b && clause (!a) (!p) (!b)

theorem anchors_iff (edited a b c p : Bool) : anchors edited a b c p = true ↔
    a = edited ∧ b = false ∧ c = false ∧ p = !edited := by
  cases edited <;> cases a <;> cases b <;> cases c <;> cases p <;> decide

/-- The four proper clauses associated to one original clause. -/
def guard (a b u v w t : Bool) : Bool :=
  clause (!a) u t && clause (!t) a b && clause (!t) (!u) b && clause (!t) v w

theorem guard_iff (a u v w t : Bool) : guard a false u v w t = true ↔
    t = (a && !u) ∧ (a = true → clause u v w = true) := by
  cases a <;> cases u <;> cases v <;> cases w <;> cases t <;> decide

variable {Name Row Spare : Type}

/-- A source row's three signed literals under a source assignment. -/
abbrev Rows (Name Row : Type) := Row → (Name → Bool) → Bool × Bool × Bool

def sourceSat (rows : Rows Name Row) (x : Name → Bool) : Prop :=
  ∀ i, let u := rows i x; clause u.1 u.2.1 u.2.2 = true

/-- The original filler pins and the added spare-name pins appear explicitly. Other
rail clauses of the zero-gate base are already satisfied once the anchors and
spares have the displayed values; the manuscript checks their syntactic forms. -/
def projectedModel (rows : Rows Name Row) (preset s : Spare → Bool)
    (edited a b c p : Bool) (x : Name → Bool) (t : Row → Bool) : Prop :=
  anchors edited a b c p = true ∧
  (∀ v, clause (!(x v)) a b = true) ∧
  (∀ i, clause (!(t i)) a b = true) ∧
  (∀ z, clause (s z == preset z) b c = true) ∧
  ∀ i, let u := rows i x; guard a b u.1 u.2.1 u.2.2 (t i) = true

theorem closed_model_iff (rows : Rows Name Row) (preset s : Spare → Bool)
    (a b c p : Bool) (x : Name → Bool) (t : Row → Bool) :
    projectedModel rows preset s false a b c p x t ↔
    a = false ∧ b = false ∧ c = false ∧ p = true ∧
      x = (fun _ => false) ∧ t = (fun _ => false) ∧ s = preset := by
  constructor
  · rintro ⟨h, hx, ht, hs, _⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (anchors_iff ..).mp h
    refine ⟨rfl, rfl, rfl, rfl, funext ?_, funext ?_, funext ?_⟩
    · intro v; simpa [clause] using hx v
    · intro i; simpa [clause] using ht i
    · intro z; simpa [clause] using hs z
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · intro v; rfl
    · intro i; rfl
    · intro z; simp [clause]
    · intro i; apply (guard_iff ..).mpr; simp

theorem edited_model_iff (rows : Rows Name Row) (preset s : Spare → Bool)
    (a b c p : Bool) (x : Name → Bool) (t : Row → Bool) :
    projectedModel rows preset s true a b c p x t ↔
    a = true ∧ b = false ∧ c = false ∧ p = false ∧
      s = preset ∧ t = (fun i => !(rows i x).1) ∧ sourceSat rows x := by
  constructor
  · rintro ⟨h, _, _, hs, hrows⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (anchors_iff ..).mp h
    refine ⟨rfl, rfl, rfl, rfl, funext ?_, funext ?_, ?_⟩
    · intro z; simpa [clause] using hs z
    · intro i; simpa using ((guard_iff ..).mp (hrows i)).1
    · intro i; exact ((guard_iff ..).mp (hrows i)).2 rfl
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, hx⟩
    refine ⟨by decide, ?_, ?_, ?_, ?_⟩
    · intro v; simp [clause]
    · intro i; simp [clause]
    · intro z; simp [clause]
    · intro i; apply (guard_iff ..).mpr; exact ⟨rfl, fun _ => hx i⟩

end OneBitFromPropagatedSat
