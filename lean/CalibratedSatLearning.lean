import Std

namespace CalibratedSatLearning

/-- Internal deterministic work has been absorbed into nodes. -/
inductive Rule (Query Verdict : Type) where
  | finish (v : Verdict)
  | ask (q : Query) (no yes : Rule Query Verdict)

def outcome {Q V : Type} (answer : Q → Bool) : Rule Q V → V
  | .finish v => v
  | .ask q l r => if answer q then outcome answer r else outcome answer l

def used {Q V : Type} (answer : Q → Bool) : Rule Q V → List Q
  | .finish _ => []
  | .ask q l r => q :: (if answer q then used answer r else used answer l)

/-- Every candidate returning the recorded replies produces the same claim. -/
theorem replay {Q V : Type} (a b : Q → Bool) (rule : Rule Q V)
    (agrees : ∀ q ∈ used a rule, a q = b q) :
    outcome a rule = outcome b rule := by
  induction rule with
  | finish _ => rfl
  | ask q l r il ir =>
    have same := agrees q (by simp [used])
    cases h : a q with
    | false =>
      have h' : b q = false := same.symm.trans h
      simp only [outcome, h, h', Bool.false_eq_true, ↓reduceIte]
      apply il
      intro x hx
      exact agrees x (by simp [used, h, hx])
    | true =>
      have h' : b q = true := same.symm.trans h
      simp only [outcome, h, h', ↓reduceIte]
      apply ir
      intro x hx
      exact agrees x (by simp [used, h, hx])

theorem transcript_forces_claim {W Q V : Type} (oracle : W → Q → Bool)
    (means : W → V → Prop) (rule : Rule Q V)
    (allTrials : ∀ w, means w (outcome (oracle w) rule))
    (trial other : W)
    (agrees : ∀ q ∈ used (oracle trial) rule, oracle trial q = oracle other q) :
    means other (outcome (oracle trial) rule) := by
  rw [replay (oracle trial) (oracle other) rule agrees]
  exact allTrials other

theorem bad_trial_excludes_actual {W Q V : Type} (oracle : W → Q → Bool)
    (means : W → V → Prop) (rule : Rule Q V) (actual trial : W)
    (sound : means actual (outcome (oracle actual) rule))
    (bad : ¬ means trial (outcome (oracle trial) rule)) : trial ≠ actual := by
  intro h
  exact bad (h ▸ sound)

/-- Each branch consumes one fresh fair bit. Determined requests are skipped. -/
inductive Game : Nat → Type where
  | stop (n : Nat) : Game n
  | watch {n : Nat} (l r : Game n) : Game (n+1)
  | bet {n : Nat} (guess : Bool) (l r : Game n) : Game (n+1)

def hits : {n : Nat} → Game n → Nat → Nat
  | n, _, 0 => 2^n
  | _, .stop _, _+1 => 0
  | _, .watch l r, k+1 => hits l (k+1) + hits r (k+1)
  | _, .bet false l _, k+1 => hits l k
  | _, .bet true _ r, k+1 => hits r k

/-- Paths with k successful fresh bets before a loss have mass at most 2⁻ᵏ,
    even with arbitrary calibration branches and a path-dependent stop. -/
theorem hits_bound {n : Nat} (g : Game n) (k : Nat) :
    2^k * hits g k ≤ 2^n := by
  induction g generalizing k with
  | stop n => cases k <;> simp [hits]
  | @watch n l r il ir =>
    cases k with
    | zero => simp [hits]
    | succ k =>
      rw [hits, Nat.mul_add, Nat.pow_succ 2 n]
      have := il (k+1)
      have := ir (k+1)
      omega
  | @bet n guess l r il ir =>
    cases k with
    | zero => simp [hits]
    | succ k =>
      cases guess
      · rw [hits, Nat.pow_succ 2 k, Nat.pow_succ 2 n, Nat.mul_right_comm]
        exact Nat.mul_le_mul_right 2 (il k)
      · rw [hits, Nat.pow_succ 2 k, Nat.pow_succ 2 n, Nat.mul_right_comm]
        exact Nat.mul_le_mul_right 2 (ir k)

end CalibratedSatLearning
