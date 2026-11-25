import Std

namespace OneByteCoreSuccessors

/-- A fixed base formula and a number of extra bytes encoded in its flexible clauses. -/
structure State where
  base : Nat
  extra : Nat
deriving DecidableEq

def size (B : Nat → Nat) (s : State) := B s.base + s.extra

def step (B : Nat → Nat) (s : State) : State :=
  if size B s + 1 = B (s.base+1) then ⟨s.base+1, 0⟩
  else ⟨s.base, s.extra+1⟩

/-- Every next byte uses either the same base or exactly the next one, even
    when the widths of adjacent allowable intervals change. -/
theorem step_ok (B : Nat → Nat) (inc : ∀ j, B j < B (j+1)) (s : State)
    (inside : size B s < B (s.base+1)) :
    size B (step B s) = size B s + 1 ∧
    size B (step B s) < B ((step B s).base+1) ∧
    ((step B s).base = s.base ∨ (step B s).base = s.base+1) := by
  by_cases hit : size B s + 1 = B (s.base+1)
  · rw [show step B s = ⟨s.base+1, 0⟩ from if_pos hit]
    exact ⟨by simpa [size] using hit.symm, by simpa [size] using inc (s.base+1), Or.inr rfl⟩
  · rw [show step B s = ⟨s.base, s.extra+1⟩ from if_neg hit]
    simp only [size] at *
    exact ⟨by omega, by omega, Or.inl trivial⟩

def atOffset (B : Nat → Nat) : Nat → State
  | 0 => ⟨0, 0⟩
  | t+1 => step B (atOffset B t)

theorem every_byte (B cap : Nat → Nat) (inc : ∀ j, B j < B (j+1))
    (fits : ∀ j, B (j+1) ≤ B j + cap j + 1) (t : Nat) :
    let s := atOffset B t
    size B s = B 0 + t ∧ size B s < B (s.base+1) ∧ s.extra ≤ cap s.base := by
  induction t with
  | zero => simpa [atOffset, size] using inc 0
  | succ t ih =>
    rcases ih with ⟨n, inRange, _⟩
    obtain ⟨ns, ins, _⟩ := step_ok B inc (atOffset B t) inRange
    change size B (step B (atOffset B t)) = B 0 + (t+1) ∧ _
    refine ⟨by omega, ins, ?_⟩
    let s := step B (atOffset B t)
    change s.extra ≤ cap s.base
    have i : B s.base + s.extra < B (s.base+1) := ins
    have f := fits s.base
    omega

/-- A single independently variable field from each interval realizes the
    whole sum interval; this handles both digit counts and optional signs. -/
theorem split_slack (a b u : Nat) (fits : u ≤ a+b) :
    ∃ x y, x ≤ a ∧ y ≤ b ∧ u = x+y := by
  exact ⟨min a u, u-min a u, by omega, by omega, by omega⟩

/-- At the endpoint, the one-step deficit cancels the possible initial
    branch-free segment. Only counts of low initial words enter stock. -/
theorem endpoint_capacity (m C stock U B : Nat)
    (data : 2*m ≤ U+stock) (segments : U ≤ C*(B+1))
    (clock : U+B+1 ≤ 2*m) : 2*m ≤ (C+1)*stock := by
  have paid : (C+1)*U ≤ C*(U+B+1) := by
    rw [Nat.succ_mul]
    rw [show U+B+1 = U+(B+1) by omega, Nat.mul_add]
    omega
  have costs := Nat.mul_le_mul_left C clock
  have raw := Nat.mul_le_mul_left (C+1) data
  rw [Nat.mul_add] at raw
  rw [Nat.succ_mul C (2*m)] at raw
  omega

end OneByteCoreSuccessors
