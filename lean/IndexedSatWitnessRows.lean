import Std

namespace IndexedSatWitnessRows

/-- A unary length can identify a row while growing linearly in its payload
    on every fixed row. -/
def slot : Nat → Nat → Nat
  | 0, u => 2 * u + 1
  | r + 1, u => 2 * slot r u

theorem slot_eq (r u : Nat) : slot r u = 2 ^ r * (2 * u + 1) := by
  induction r with
  | zero => simp [slot]
  | succ r ih => simp [slot, ih, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem slot_injective {r s u v : Nat} (h : slot r u = slot s v) :
    r = s ∧ u = v := by
  induction r generalizing s with
  | zero =>
    cases s with
    | zero => simp [slot] at h; omega
    | succ s => simp [slot] at h; omega
  | succ r ih =>
    cases s with
    | zero => simp [slot] at h; omega
    | succ s =>
      simp only [slot] at h
      obtain ⟨ers, euv⟩ := ih (s := s) (by omega)
      exact ⟨congrArg Nat.succ ers, euv⟩

theorem slot_grows (r u : Nat) : u < slot r u := by
  induction r with
  | zero => simp [slot]; omega
  | succ r ih => simp only [slot]; omega

/-- At a dyadic length there are as many different unary payloads as there
    are bytes in the file, all before the following dyadic length. -/
theorem dyadic_unique {a b j k : Nat} (hj : j < 2 ^ a) (hk : k < 2 ^ b)
    (h : 2 ^ a + j = 2 ^ b + k) : a = b ∧ j = k := by
  have no_gap (v w z : Nat) (hz : z < 2 ^ v) (hvw : v < w) :
      2 ^ v + z < 2 ^ w := by
    have hstep : 2 ^ (v+1) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by decide) hvw
    simp only [Nat.pow_succ] at hstep
    omega
  have e : a = b := by
    rcases Nat.lt_trichotomy a b with lt | eq | gt
    · have := no_gap a b j hj lt; omega
    · exact eq
    · have := no_gap b a k hk gt; omega
  constructor
  · exact e
  · subst b; omega

/-- The signed records are the bounded outputs that finished in time.
    Inspection may stop as soon as the actual input has an exact match. -/
def answer [DecidableEq X] (fallback : X → Bool) (x : X) :
    List (X × Bool) → Bool
  | [] => fallback x
  | (y, b) :: ys => if x = y then b else answer fallback x ys

theorem answer_correct [DecidableEq X] (truth : X → Bool) (x : X)
    (ys : List (X × Bool)) (h : ∀ e ∈ ys, e.2 = truth e.1) :
    answer truth x ys = truth x := by
  induction ys with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨y, b⟩
    by_cases he : x = y
    · subst y; simpa [answer] using h (x, b) (by simp)
    · simp only [answer, if_neg he]
      exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

end IndexedSatWitnessRows
