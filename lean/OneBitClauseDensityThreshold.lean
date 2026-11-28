import Std

namespace OneBitClauseDensityThreshold

def clause (a b c : Bool) := a || b || c

theorem four_pins : ∀ old fresh left right : Bool,
    (clause old left right = true ∧ clause fresh left right = false) ↔
    old = true ∧ fresh = false ∧ left = false ∧ right = false := by decide +kernel

private def forceOff (f a b : Bool) :=
  clause (!f) a b && clause (!f) a (!b) &&
  clause (!f) (!a) b && clause (!f) (!a) (!b)

def controls (easy a b f g : Bool) :=
  forceOff f a b && forceOff g a b && clause a b f &&
  clause (!a) (!b) f && clause (if easy then a else b) f g

theorem four_controls : ∀ easy a b f g : Bool,
    controls easy a b f g = true ↔
    a = easy ∧ b = !easy ∧ f = false ∧ g = false := by decide +kernel

def tie (b y literal : Bool) :=
  clause (!b) (!y) literal && clause (!b) y (!literal)

theorem copied_value : ∀ b y lit : Bool,
    tie b y lit = true ↔ b = false ∨ y = lit := by decide +kernel

theorem private_pin : ∀ u : Bool,
    clause (!true) u false = u ∧ clause (!false) u false = true := by decide +kernel

theorem free_private_pair : ∀ p q : Bool, clause true p q = true := by decide +kernel

theorem forced_private_pair : ∀ guard : Bool, clause guard true true = true := by decide +kernel

theorem physical_bit : (('3'.toNat) ^^^ ('1'.toNat)) = 2 := by decide +kernel

/-- Four pins have probability 1/16.  The independent occurrence clauses
    have model fraction 7^m / 8^m, and the transversal is m+4. -/
theorem density_equality (m : Nat) :
    7^m * 8^(m+4) * 7^4 = (16 * 8^m) * 7^(m+4) * 4^4 := by
  simp only [Nat.pow_add]
  have h : (8:Nat)^4 = 16 * 4^4 := by decide +kernel
  rw [h]
  ac_rfl


def Hits (h : List (List Nat)) (s : List Nat) : Prop :=
  ∀ e ∈ h, ∃ v, v ∈ e ∧ v ∈ s

def untouched (h : List (List Nat)) (pins : List Nat) :=
  h.filter fun e => !(pins.any fun v => e.contains v)

/-- A transversal of the unchanged ternaries and the pinned variables
    together meet every old clause, for any number of pins. -/
theorem lift_untouched {h : List (List Nat)} {s pins : List Nat}
    (hs : Hits (untouched h pins) s) : Hits h (pins ++ s) := by
  intro e he
  by_cases hi : ∃ v, v ∈ pins ∧ v ∈ e
  · obtain ⟨v, hp, hv⟩ := hi
    exact ⟨v,hv,List.mem_append_left _ hp⟩
  · have mem : e ∈ untouched h pins := by
      apply List.mem_filter.mpr
      simpa [List.any_eq_true, he] using hi
    obtain ⟨v, hv, hin⟩ := hs _ mem
    exact ⟨v,hv,List.mem_append_right _ hin⟩

theorem needs_after_pins {h : List (List Nat)} (pins : List Nat) (t : Nat)
    (need : ∀ s, Hits h s → t + pins.length ≤ s.length) :
    ∀ s, Hits (untouched h pins) s → t ≤ s.length := by
  intro s hs
  have count := need (pins ++ s) (lift_untouched hs)
  simp only [List.length_append] at count
  omega

theorem normalized_after_four (models ambient t : Nat)
    (residual_bound : models * 8^t ≤ ambient * 7^t) :
    models * 8^(t+4) * 7^4 ≤ (16 * ambient) * 7^(t+4) * 4^4 := by
  rw [Nat.pow_add, Nat.pow_add]
  calc
    _ = (models * 8^t) * (8^4 * 7^4) := by ac_rfl
    _ ≤ (ambient * 7^t) * (8^4 * 7^4) := Nat.mul_le_mul_right _ residual_bound
    _ = _ := by
      have eq : (8:Nat)^4 = 16 * 4^4 := by decide +kernel
      rw [eq]
      ac_rfl

end OneBitClauseDensityThreshold
