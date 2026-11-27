import Std

namespace TwoAnswerParity

/-- One shared Boolean address compared between two tests, each with at most
    two admissible local vectors. Duplicate a singleton vector. -/
inductive Link where
  | free | impossible | leftPin (value : Bool) | rightPin (value : Bool) | edge (sign : Bool)

def shared (a₀ a₁ b₀ b₁ : Bool) : Link :=
  if a₀ == a₁ then
    if b₀ == b₁ then (if a₀ == b₀ then .free else .impossible)
    else .rightPin (a₀ ^^ b₀)
  else if b₀ == b₁ then .leftPin (a₀ ^^ b₀)
  else .edge (a₀ ^^ b₀)

def honors (x y : Bool) : Link → Prop
  | .free => True
  | .impossible => False
  | .leftPin a => x = a
  | .rightPin b => y = b
  | .edge sign => (x ^^ y) = sign

theorem shared_exact (a₀ a₁ b₀ b₁ x y : Bool) :
    honors x y (shared a₀ a₁ b₀ b₁) ↔
      (if x then a₁ else a₀) = (if y then b₁ else b₀) := by
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> cases x <;> cases y <;>
    simp [honors, shared]

variable {V : Type}
abbrev Walk (V : Type) := List (V × Bool)

def lastVertex (start : V) : Walk V → V
  | [] => start
  | (v, _) :: rest => lastVertex v rest

def parity : Walk V → Bool
  | [] => false
  | (_, b) :: rest => b ^^ parity rest

def follows (value : V → Bool) (start : V) : Walk V → Prop
  | [] => True
  | (v, b) :: rest => value v = (value start ^^ b) ∧ follows value v rest

theorem endpoint (value : V → Bool) (start : V) (p : Walk V)
    (ok : follows value start p) :
    value (lastVertex start p) = (value start ^^ parity p) := by
  induction p generalizing start with
  | nil => simp [lastVertex, parity]
  | cons head tail ih =>
    obtain ⟨v, b⟩ := head
    obtain ⟨first, later⟩ := ok
    simpa [lastVertex, parity, first, Bool.xor_assoc] using ih v later

/-- Two root paths plus one edge are inconsistent if their signs conflict. -/
theorem bad_edge (root : V) (p q : Walk V) (sign : Bool)
    (conflict : (parity p ^^ parity q) ≠ sign) :
    ¬ ∃ value, follows value root p ∧ follows value root q ∧
      (value (lastVertex root p) ^^ value (lastVertex root q)) = sign := by
  rintro ⟨value, hp, hq, edge⟩
  rw [endpoint value root p hp, endpoint value root q hq] at edge
  cases a : value root <;> cases b : parity p <;> cases c : parity q <;>
    simp_all

/-- The values prescribed at two endpoints cannot require opposite values
    at their common root. The two tests supplying the pins can lie outside
    the paths, so their provenance must be kept in the original witness. -/
theorem bad_pins (root : V) (p q : Walk V) (a b : Bool)
    (conflict : (a ^^ parity p) ≠ (b ^^ parity q)) :
    ¬ ∃ value, follows value root p ∧ follows value root q ∧
      value (lastVertex root p) = a ∧ value (lastVertex root q) = b := by
  rintro ⟨value, hp, hq, leftPin, rightPin⟩
  rw [endpoint value root p hp] at leftPin
  rw [endpoint value root q hq] at rightPin
  cases u : value root <;> cases v : parity p <;> cases w : parity q <;> simp_all

/-- Integral form of the ball-growth argument. The ratio is p/d > 1 in the
    application; the conclusion says that a step has sufficiently small growth. -/
theorem small_growth (volume : Nat → Nat) (p d limit rounds : Nat)
    (starts : 1 ≤ volume 0) (ends : volume rounds ≤ limit)
    (large : d^rounds * limit < p^rounds) :
    ∃ i < rounds, d * volume (i+1) ≤ p * volume i := by
  apply Classical.byContradiction
  intro none
  have growth : ∀ i < rounds, p * volume i ≤ d * volume (i+1) := by
    intro i hi
    exact Nat.le_of_lt (Nat.lt_of_not_ge (fun small => none ⟨i, hi, small⟩))
  have power : ∀ i ≤ rounds, p^i ≤ d^i * volume i := by
    intro i
    induction i with
    | zero => simpa using (fun _ : 0 ≤ rounds => starts)
    | succ i ih =>
      intro hi
      have prev := ih (by omega)
      calc
        p^(i+1) = p^i * p := Nat.pow_succ p i
        _ ≤ (d^i * volume i) * p := Nat.mul_le_mul_right p prev
        _ = d^i * (p * volume i) := by ac_rfl
        _ ≤ d^i * (d * volume (i+1)) := Nat.mul_le_mul_left _ (growth i (by omega))
        _ = d^(i+1) * volume (i+1) := by rw [Nat.pow_succ]; ac_rfl
  have bound := Nat.le_trans (power rounds (by omega)) (Nat.mul_le_mul_left (d^rounds) ends)
  omega

end TwoAnswerParity
