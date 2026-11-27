import Std

namespace PhysicalSelectorParity

/-- Every consecutive directed implication, starting at x and ending at y. -/
def chain (x : Bool) : List Bool → Bool → Prop
  | [], y => x = true → y = true
  | z :: zs, y => (x = true → z = true) ∧ chain z zs y

theorem propagate {x y : Bool} {zs : List Bool} (h : chain x zs y) :
    (x = true → y = true) ∧
    ∀ b ∈ zs, (x = true → b = true) ∧ (b = true → y = true) := by
  induction zs generalizing x with
  | nil => exact ⟨h, by simp⟩
  | cons a as ih =>
    obtain ⟨xa, ha⟩ := h
    obtain ⟨ay, between⟩ := ih ha
    refine ⟨fun hx => ay (xa hx), ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with hba | hbas
    · subst b
      exact ⟨xa, ay⟩
    · obtain ⟨ab, by'⟩ := between b hbas
      exact ⟨fun hx => ab (xa hx), by'⟩

theorem cycle_uniform (t : Bool) (zs : List Bool) (h : chain t zs t) :
    ∀ b ∈ zs, b = t := by
  intro b hb
  obtain ⟨forward, backward⟩ := (propagate h).2 b hb
  cases t <;> cases b <;> simp_all

/-- The signed copies -a and +b are on the cycle for t. The external clause
    selects +a or +b after the two false padding literals have been eliminated. -/
def realizesBit (z t : Bool) : Prop :=
  ∃ a b : Bool, chain t [!a, b] t ∧ (if z then b else a) = true

theorem selector_iff (z t : Bool) : realizesBit z t ↔ z = t := by
  constructor
  · rintro ⟨a, b, h, selected⟩
    have ha := cycle_uniform t [!a, b] h (!a) (by simp)
    have hb := cycle_uniform t [!a, b] h b (by simp)
    cases z <;> cases t <;> cases a <;> cases b <;> simp_all
  · rintro rfl
    refine ⟨!z, z, ?_, ?_⟩ <;> cases z <;> simp [chain]

def coordinates : List Bool → List Bool → Prop
  | [], [] => True
  | z :: zs, t :: ts => realizesBit z t ∧ coordinates zs ts
  | _, _ => False

theorem coordinates_iff (zs ts : List Bool) : coordinates zs ts ↔ zs = ts := by
  induction zs generalizing ts with
  | nil => cases ts <;> simp [coordinates]
  | cons z zs ih => cases ts <;> simp [coordinates, selector_iff, ih]

def parity : List Bool → Bool
  | [] => false
  | b :: bs => xor b (parity bs)

theorem projected_corners (mask : List Bool) (sat : Bool → Prop) :
    (∃ inputs, coordinates mask inputs ∧ sat (parity inputs)) ↔ sat (parity mask) := by
  constructor
  · rintro ⟨inputs, actual, proof⟩
    rwa [← (coordinates_iff _ _).1 actual] at proof
  · exact fun h => ⟨mask, (coordinates_iff _ _).2 rfl, h⟩

theorem split_guarded_clause (guard a b c : Bool) :
    (∃ y : Bool, (guard || a || y) = true ∧ (!y || b || c) = true) ↔
    (guard || a || b || c) = true := by
  cases guard <;> cases a <;> cases b <;> cases c <;> decide

/-- The maximal lower interval and the minimal upper interval miss one
    integer when the old names are saturated at the end of a decade. -/
theorem last_padding_gap (d s : Nat) :
    (s ≤ d+2 → 1+s*(3*d+11)+1 ≤ (d+3)*(3*d+8)) ∧
    (d+3 ≤ s → (d+3)*(3*d+8) < 1+s*(3*d+8)) := by
  constructor
  · intro hs
    have h := Nat.mul_le_mul_right (3*d+11) hs
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm d 3, Nat.mul_assoc] at h ⊢
    omega
  · intro hs
    have h := Nat.mul_le_mul_right (3*d+8) hs
    omega

/-- If one appended clause costs 3d+8 bytes before signs, the net one-byte
    change forces every old extension clause to be deleted at the first
    count transition above the worst-case conductor. -/
theorem loss_of_every_added_row (d oldSigns newSigns removed : Nat)
    (byteStep : 3*d+8+newSigns = oldSigns+1)
    (commonRowsKeepSigns : oldSigns ≤ newSigns + 3*removed)
    (budget : removed ≤ d+3) : removed = d+3 := by omega

end PhysicalSelectorParity
