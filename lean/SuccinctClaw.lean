import Std

namespace SuccinctClaw

/-- Writes to a fixed address and one bit of its word. -/
def before (write : Nat → Option Bool) : Nat → Bool
  | 0 => false
  | t + 1 => (write t).getD (before write t)

def anchored (write : Nat → Option Bool) (b : Bool) (cut : Nat) : Prop :=
  (cut = 0 ∧ b = false) ∨ ∃ s, cut = s + 1 ∧ write s = some b

def unopposed (write : Nat → Option Bool) (b : Bool) (cut t : Nat) : Prop :=
  ∀ s, cut ≤ s → s < t → write s ≠ some (!b)

theorem anchor_sound {write : Nat → Option Bool} {b : Bool} {cut t : Nat}
    (hcut : cut ≤ t) (anchor : anchored write b cut) (clear : unopposed write b cut t) :
    before write t = b := by
  have start : before write cut = b := by
    rcases anchor with ⟨rfl, rfl⟩ | ⟨s, rfl, hw⟩
    · rfl
    · simp [before, hw]
  induction t with
  | zero =>
    have hc : cut = 0 := by omega
    simpa [hc] using start
  | succ t ih =>
    by_cases eq : cut = t + 1
    · simpa [eq] using start
    · have le : cut ≤ t := by omega
      have prior := ih le (fun s hs ht => clear s hs (by omega))
      have no := clear t le (by omega)
      cases hw : write t with
      | none => simpa [before, hw] using prior
      | some v =>
        cases v <;> cases b <;> simp_all [before]

theorem anchor_iff (write : Nat → Option Bool) (b : Bool) (t : Nat) :
    before write t = b ↔ ∃ cut ≤ t, anchored write b cut ∧ unopposed write b cut t := by
  constructor
  · induction t with
    | zero =>
      intro h
      exact ⟨0, Nat.le_refl _, Or.inl ⟨rfl, h.symm⟩, fun _ _ ht => by omega⟩
    | succ t ih =>
      intro h
      cases hw : write t with
      | some v =>
        have hb : v = b := by simpa [before, hw] using h
        exact ⟨t+1, Nat.le_refl _, Or.inr ⟨t, rfl, hb ▸ hw⟩, fun _ hs ht => by omega⟩
      | none =>
        obtain ⟨cut, le, start, clear⟩ := ih (by simpa [before, hw] using h)
        refine ⟨cut, by omega, start, fun s hs ht => ?_⟩
        by_cases last : s = t
        · simp [last, hw]
        · exact clear s hs (by omega)
  · rintro ⟨cut, le, start, clear⟩
    exact anchor_sound le start clear

/-- A common key must occur precisely when a store is inside the load gap.
The concrete implementation uses maximal dyadic intervals. -/
theorem separated_gap {Cell : Type} {write : Nat → Option Bool} {b : Bool}
    {cut t : Nat} (has : Nat → Cell → Prop) (cover : Cell → Prop)
    (covered : ∀ s, cut ≤ s → s < t → ∃ c, has s c ∧ cover c)
    (mark : Cell → Bool → Bool)
    (stores : ∀ s c v, write s = some v → has s c → mark c v = true)
    (loads : ∀ c, cover c → mark c (!b) = false) :
    unopposed write b cut t := by
  intro s lower upper opposite
  obtain ⟨c, member, active⟩ := covered s lower upper
  have h := stores s c (!b) opposite member
  rw [loads c active] at h
  contradiction

/-- One layer of a causal word permutation. A row's side symbol is preserved.
For each preceding state the transformation on the current word is involutive. -/
def forward (twist : G → W → W → W) (prev : W) : List (G × W) → List (G × W)
  | [] => []
  | (g, s) :: rest => (g, twist g prev s) :: forward twist s rest

def backward (twist : G → W → W → W) (prev : W) : List (G × W) → List (G × W)
  | [] => []
  | (g, out) :: rest =>
    let s := twist g prev out
    (g, s) :: backward twist s rest

theorem backward_forward (twist : G → W → W → W)
    (undo : ∀ g prev s, twist g prev (twist g prev s) = s)
    (prev : W) (rows : List (G × W)) :
    backward twist prev (forward twist prev rows) = rows := by
  induction rows generalizing prev with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨g,s⟩ := row
    simp [forward, backward, undo, ih]

theorem forward_backward (twist : G → W → W → W)
    (undo : ∀ g prev s, twist g prev (twist g prev s) = s)
    (prev : W) (rows : List (G × W)) :
    forward twist prev (backward twist prev rows) = rows := by
  induction rows generalizing prev with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨g,s⟩ := row
    simp [forward, backward, undo, ih]

end SuccinctClaw
