import Std

namespace RefereeSupport

variable {Coin LeftQuestion RightQuestion LeftAnswer RightAnswer : Type}
variable (left : Coin → LeftQuestion) (right : Coin → RightQuestion)
variable (win : Coin → LeftAnswer → RightAnswer → Prop)

/-- A refutation must defeat every pure policy of the left player on every coin. -/
def Refutes : Prop :=
  ∃ policy : RightQuestion → RightAnswer,
    ∀ (rival : LeftQuestion → LeftAnswer) (r : Coin),
      ¬ win r (rival (left r)) (policy (right r))

/-- A single right question can force every reply to have a losing transcript.
    Its coin and the left reply may depend on the proposed right reply. -/
theorem positive_support :
    (¬ Refutes left right win) ↔
    ∃ v, ∀ b, ∃ r a, right r = v ∧ win r a b := by
  classical
  constructor
  · intro noRefute
    apply Classical.byContradiction
    intro missing
    have safe : ∀ v, ∃ b, ¬ ∃ r a, right r = v ∧ win r a b := by
      intro v
      apply Classical.byContradiction
      intro noSafe
      apply missing
      refine ⟨v, fun b => ?_⟩
      exact Classical.byContradiction (fun bad => noSafe ⟨b, bad⟩)
    apply noRefute
    refine ⟨fun v => Classical.choose (safe v), ?_⟩
    intro rival r h
    exact Classical.choose_spec (safe (right r)) ⟨r, rival (left r), rfl, h⟩
  · rintro ⟨v, h⟩ ⟨policy, defeats⟩
    obtain ⟨r, a, eq, success⟩ := h (policy v)
    have fail := defeats (fun _ => a) r
    rw [eq] at fail
    exact fail success

/-- If membership of the two witnessed sets is incompatible, a pure high
    row for a finite panel and a pure low column cannot both be certified. -/
theorem exclusive {Row Col : Type} (pass : Row → Col → Prop)
    (high : ∃ row, ∀ col, pass row col)
    (low : ∃ col, ∀ row, ¬ pass row col) : False := by
  obtain ⟨row, hr⟩ := high
  obtain ⟨col, hc⟩ := low
  exact hc row (hr col)

/-- Scaled gate variables and a scaled maximum constraint violation.
    The copy-AND and its OR successor imply the recurrence below. -/
theorem chain_slack (x : Nat → Nat) (err : Nat) (init : x 0 ≤ err)
    (step : ∀ i, x (i+1) ≤ 2*x i + 2*err) (h total : Nat)
    (outputPin : total ≤ x h + err) :
    total + err ≤ 2^h * (3*err) := by
  have bounded : ∀ i : Nat, x i + 2*err ≤ 2^i * (3*err) := by
    intro i
    induction i with
    | zero => simp; omega
    | succ i ih =>
      have next := step i
      calc
        x (i+1) + 2*err ≤ 2*(x i + 2*err) := by omega
        _ ≤ 2*(2^i * (3*err)) := Nat.mul_le_mul_left 2 ih
        _ = 2^(i+1) * (3*err) := by rw [Nat.pow_succ]; ac_rfl
  have atEnd := bounded h
  omega

end RefereeSupport
