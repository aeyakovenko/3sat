import Mathlib.Logic.Function.Iterate

/-! Exact-length endpoint lists with an existential list and a universal segment.
The state may itself contain arbitrary tape contents. -/

namespace CheckpointEndpointLists

open Function

theorem split_run {X : Type*} (step : X → X) (b t : ℕ) (x y : X) :
    step^[b*t] x = y ↔
    ∃ c : ℕ → X, c 0 = x ∧ c b = y ∧
      ∀ j < b, step^[t] (c j) = c (j+1) := by
  constructor
  · intro h
    refine ⟨fun j => step^[j*t] x, by simp, h, ?_⟩
    intro j _
    simp only [Nat.add_mul, Nat.one_mul]
    rw [Nat.add_comm (j*t) t, Function.iterate_add_apply]
  · rintro ⟨c, c0, cb, links⟩
    have toEndpoint : ∀ j ≤ b, step^[j*t] x = c j := by
      intro j
      induction j with
      | zero => intro _; simpa using c0.symm
      | succ j ih =>
        intro bound
        rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
        exact links j (by omega)
    exact (toEndpoint b (Nat.le_refl b)).trans cb

def game {X : Type*} (step : X → X) (fanout : ℕ) : ℕ → X → X → Prop
  | 0, x, y => step x = y
  | k+1, x, y =>
    ∃ c : ℕ → X, c 0 = x ∧ c fanout = y ∧
      ∀ j < fanout, game step fanout k (c j) (c (j+1))

theorem game_iff_iterate {X : Type*} (step : X → X) (b k : ℕ) (x y : X) :
    game step b k x y ↔ step^[b^k] x = y := by
  induction k generalizing x y with
  | zero => simp [game]
  | succ k ih =>
    simp only [game, ih, Nat.pow_succ, Nat.mul_comm (b^k) b]
    exact (split_run step b (b^k) x y).symm

#print axioms game_iff_iterate

end CheckpointEndpointLists
