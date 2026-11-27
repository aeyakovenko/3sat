import Std

namespace PhaseAccess

/-- The phase number is nondecreasing along chronological time. -/
def Ordered (phase : Nat → Nat) : Prop :=
  ∀ ⦃i j⦄, i ≤ j → phase i ≤ phase j

private theorem time_lt {phase : Nat → Nat} (ord : Ordered phase) {i j : Nat}
    (earlier : phase i < phase j) : i < j := by
  by_cases reversed : j ≤ i
  · have := ord reversed
    omega
  · omega

/-- There is no access to the given address strictly between the two rows. -/
def Adjacent (visits : Nat → Prop) (u t : Nat) : Prop :=
  u < t ∧ visits u ∧ visits t ∧ ∀ i, u < i → i < t → ¬visits i

/-- The overwrite map excludes every intervening phase at this address. -/
def Skips (phase : Nat → Nat) (visits : Nat → Prop) (q p : Nat) : Prop :=
  ∀ i, q < phase i → phase i < p → ¬visits i

def FirstIn (phase : Nat → Nat) (visits : Nat → Prop) (t : Nat) : Prop :=
  ∀ i, i < t → phase i = phase t → ¬visits i

def LastIn (phase : Nat → Nat) (visits : Nat → Prop) (u : Nat) : Prop :=
  ∀ i, u < i → phase i = phase u → ¬visits i

/-- When u and t lie in distinct phases, the two local endpoint tests and the
    overwrite map are necessary and sufficient to recognize a true predecessor. -/
theorem between_phases (phase : Nat → Nat) (visits : Nat → Prop)
    (ord : Ordered phase) {u t : Nat} (before : phase u < phase t)
    (hu : visits u) (ht : visits t) :
    Adjacent visits u t ↔
      LastIn phase visits u ∧ Skips phase visits (phase u) (phase t) ∧ FirstIn phase visits t := by
  have chronological : u < t := time_lt ord before
  constructor
  · rintro ⟨_, _, _, gap⟩
    constructor
    · intro i hui same
      apply gap i hui
      exact time_lt ord (by omega)
    constructor
    · intro i left right
      apply gap i
      · exact time_lt ord (by omega)
      · exact time_lt ord (by omega)
    · intro i hit same
      apply gap i _ hit
      exact time_lt ord (by omega)
  · rintro ⟨last, skips, first⟩
    refine ⟨chronological, hu, ht, ?_⟩
    intro i hui hit
    have lo := ord (Nat.le_of_lt hui)
    have hi := ord (Nat.le_of_lt hit)
    by_cases left : phase i = phase u
    · exact last i hui left
    by_cases right : phase i = phase t
    · exact first i hit right
    exact skips i (by omega) (by omega)

/-- If two rows share a phase, every intermediate row belongs to it. -/
theorem within_phase (phase : Nat → Nat) (visits : Nat → Prop)
    (ord : Ordered phase) {u t : Nat} (same : phase u = phase t)
    (before : u < t) (hu : visits u) (ht : visits t) :
    Adjacent visits u t ↔
      ∀ i, u < i → i < t → phase i = phase t → ¬visits i := by
  constructor
  · intro h i hui hit _
    exact h.2.2.2 i hui hit
  · intro localGap
    refine ⟨before, hu, ht, ?_⟩
    intro i hui hit
    have lo := ord (Nat.le_of_lt hui)
    have hi := ord (Nat.le_of_lt hit)
    exact localGap i hui hit (by omega)

/-- The untouched label plus the phase-local first-visit check justifies using
    the initial value, even when the current phase has many other addresses. -/
theorem first_global (phase : Nat → Nat) (visits : Nat → Prop)
    (ord : Ordered phase) (t : Nat) :
    (∀ i, i < t → ¬ visits i) ↔
      (∀ i, phase i < phase t → ¬ visits i) ∧ FirstIn phase visits t := by
  constructor
  · intro h
    constructor
    · intro i earlier
      apply h i
      exact time_lt ord (by omega)
    · exact fun i hi _ => h i hi
  · rintro ⟨old, first⟩ i hi
    have le := ord (Nat.le_of_lt hi)
    by_cases same : phase i = phase t
    · exact first i hi same
    · exact old i (by omega)

/-- Each node stores the proposed occupancy bit for one fixed address. -/
inductive Occupancy where
  | leaf (reported visited : Bool)
  | fork (reported : Bool) (left right : Occupancy)

def Occupancy.bit : Occupancy → Bool
  | .leaf reported _ | .fork reported _ _ => reported

def Occupancy.hasVisit : Occupancy → Bool
  | .leaf _ visited => visited
  | .fork _ l r => l.hasVisit || r.hasVisit

def Occupancy.valid : Occupancy → Prop
  | .leaf reported visited => reported = visited
  | .fork reported l r => reported = (l.bit || r.bit) ∧ l.valid ∧ r.valid

theorem Occupancy.exact (t : Occupancy) (h : t.valid) : t.bit = t.hasVisit := by
  induction t with
  | leaf reported visited => exact h
  | fork reported l r il ir =>
    obtain ⟨root, left, right⟩ := h
    exact root.trans (by rw [il left, ir right]; rfl)

end PhaseAccess
