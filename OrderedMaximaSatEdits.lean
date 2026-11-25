import Std

namespace OrderedMaximaSatEdits

abbrev Triple := Bool × Bool × Bool

/-- Each coordinate specifies the polarity of the corresponding variable. -/
def satisfies (v c : Triple) : Prop :=
  v.1 = c.1 ∨ v.2.1 = c.2.1 ∨ v.2.2 = c.2.2

def target : Triple := (true, false, true)

def exclude (v : Triple) : Triple := (!v.1, !v.2.1, !v.2.2)

def fixedClauses (v : Triple) : Prop :=
  ∀ z : Triple, z ≠ target → satisfies v (exclude z)

theorem exclude_iff (v z : Triple) : satisfies v (exclude z) ↔ v ≠ z := by
  unfold satisfies exclude
  obtain ⟨a, b, c⟩ := v
  obtain ⟨d, e, f⟩ := z
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem fixed_iff (v : Triple) : fixedClauses v ↔ v = target := by
  constructor
  · intro h
    by_cases hn : v = target
    · exact hn
    · exact False.elim ((exclude_iff v v).mp (h v hn) rfl)
  · rintro rfl z hn
    exact (exclude_iff target z).mpr (Ne.symm hn)

/-- Clause j after flipping the first polarity in the record for i. -/
def record {m : Nat} (bits : Fin m → Bool) (i j : Fin m) : Triple :=
  (decide (j ≠ i), true, bits j)

theorem sat_after_edit {m : Nat} (bits : Fin m → Bool) (i : Fin m) :
    (∃ v, fixedClauses v ∧ ∀ j, satisfies v (record bits i j)) ↔ bits i = true := by
  constructor
  · rintro ⟨v, hv, hj⟩
    have eq := (fixed_iff v).mp hv
    subst v
    have hx : true = bits i := by simpa [satisfies, target, record] using hj i
    exact hx.symm
  · intro h
    refine ⟨target, (fixed_iff target).mpr rfl, ?_⟩
    intro j
    by_cases eq : j = i
    · subst j
      simp [satisfies, target, record, h]
    · simp [satisfies, target, record, eq]

end OrderedMaximaSatEdits
