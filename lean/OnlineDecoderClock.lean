import Std

namespace OnlineDecoderClock

/-- One completed native round includes all decoder instructions paid during it.
The state includes the decoder's mutable workspace and the guest's local log. -/
abbrev Round (State : Type) := State → Option (State × Nat)

inductive Finishes {State : Type} (round : Round State) :
    Nat → State → State → Nat → Prop
  | zero (s) : Finishes round 0 s s 0
  | next {n s middle final cost rest} (step : round s = some (middle, cost))
      (tail : Finishes round n middle final rest) :
      Finishes round (n + 1) s final (cost + rest)

/-- Finite semantics for a cumulative clock. An operational interpreter can
interrupt a partial round as soon as the remaining instruction budget expires. -/
def replay {State : Type} (round : Round State) :
    Nat → Nat → State → Option State
  | 0, _, s => some s
  | n + 1, budget, s => do
    let (middle, cost) ← round s
    if cost ≤ budget then replay round n (budget - cost) middle else none

theorem replay_iff {State : Type} {round : Round State} {steps budget : Nat}
    {s final : State} :
    replay round steps budget s = some final ↔
      ∃ cost ≤ budget, Finishes round steps s final cost := by
  induction steps generalizing s final budget with
  | zero =>
    constructor
    · intro h
      have eq : s = final := Option.some.inj h
      subst final
      exact ⟨0, Nat.zero_le _, Finishes.zero _⟩
    · rintro ⟨_, _, run⟩
      cases run
      rfl
  | succ n ih =>
    constructor
    · intro h
      cases hr : round s with
      | none => simp [replay, hr] at h
      | some pair =>
        obtain ⟨middle, cost⟩ := pair
        by_cases fits : cost ≤ budget
        · have ht : replay round n (budget - cost) middle = some final := by
            simpa [replay, hr, fits] using h
          obtain ⟨rest, bound, tail⟩ := ih.mp ht
          exact ⟨cost + rest, by omega, Finishes.next hr tail⟩
        · simp [replay, hr, fits] at h
    · rintro ⟨total, bound, run⟩
      cases run with
      | next step tail =>
        rename_i middle cost rest
        have fits : cost ≤ budget := by omega
        have ht : replay round n (budget - cost) middle = some final :=
          ih.mpr ⟨rest, by omega, tail⟩
        simpa [replay, step, fits] using ht

/-- Integer cross-multiplication of c/2 ≤ B*c/(B+u*v).
The lower cut bound is needed when charging an amortized clock's burst. -/
theorem cut_pays_burst (c B uv : Nat) (dominates : uv ≤ B) :
    c * (B + uv) ≤ (2 * B) * c := by
  have fac : B + uv ≤ 2 * B := by omega
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left c fac

end OnlineDecoderClock
