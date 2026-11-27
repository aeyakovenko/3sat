import Std

namespace ObservableRecurrence

/-- A window argument only needs to forbid the first nonzero after r zeros. -/
theorem zero_windows {r : Nat} {e : Nat → Bool}
    (initial : ∀ i : Fin r, e i.val = false)
    (advance : ∀ t, (∀ i : Fin r, e (t + i.val) = false) → e (t + r) = false)
    (n : Nat) : e n = false := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < r
    · exact initial ⟨n, small⟩
    · have cut : n - r + r = n := by omega
      rw [← cut]
      apply advance
      intro i
      exact ih _ (by have := i.isLt; omega)

def run (step : α → α) (start : α) : Nat → α
  | 0 => start
  | t + 1 => step (run step start t)

theorem run_add (step : α → α) (start : α) (t j : Nat) :
    run step start (t + j) = run step (run step start t) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg step ih

/-- The forbidden configuration test is universal, while the initialized
    r-term zero window belongs to just one orbit. -/
theorem orbit_zero {r : Nat} (step : α → α) (discrepancy : α → Bool) (start : α)
    (initial : ∀ i : Fin r, discrepancy (run step start i.val) = false)
    (localTest : ∀ x, (∀ i : Fin r, discrepancy (run step x i.val) = false) →
      discrepancy (run step x r) = false)
    (n : Nat) : discrepancy (run step start n) = false := by
  apply zero_windows initial _ n
  intro t window
  rw [run_add]
  apply localTest
  intro i
  rw [← run_add]
  exact window i

def Follows (r : Nat) (update : (Fin r → α) → α) (u : Nat → α) : Prop :=
  ∀ t, u (t + r) = update (fun i => u (t + i.val))

theorem same_from_window {r : Nat} {update : (Fin r → α) → α} {u v : Nat → α}
    (hu : Follows r update u) (hv : Follows r update v)
    (initial : ∀ i : Fin r, u i.val = v i.val) (n : Nat) : u n = v n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < r
    · exact initial ⟨n, small⟩
    · let t := n - r
      have cut : t + r = n := by dsimp [t]; omega
      calc
        u n = u (t + r) := congrArg u cut.symm
        _ = update (fun i => u (t + i.val)) := hu t
        _ = update (fun i => v (t + i.val)) := congrArg update (funext fun i =>
          ih _ (by have := i.isLt; omega))
        _ = v (t + r) := (hv t).symm
        _ = v n := congrArg v cut

def xorDot : (r : Nat) → (Fin r → Bool) → (Fin r → Bool) → Bool
  | 0, _, _ => false
  | r + 1, a, u => (a 0 && u 0) ^^ xorDot r (fun i => a i.succ) (fun i => u i.succ)

theorem xorDot_zero (r : Nat) (a : Fin r → Bool) :
    xorDot r a (fun _ => false) = false := by
  induction r with
  | zero => rfl
  | succ r ih => simp [xorDot, ih]

/-- A homogeneous binary linear recurrence needs more slots than the number
    of initial zeros before a first pulse. -/
theorem first_pulse {r t : Nat} {u : Nat → Bool} (a : Fin r → Bool)
    (h : Follows r (xorDot r a) u) (quiet : ∀ i < t, u i = false)
    (pulse : u t = true) : t < r := by
  by_cases small : t < r
  · exact small
  have initial (i : Fin r) : u i.val = false := quiet _ (by have := i.isLt; omega)
  have zeros : Follows r (xorDot r a) (fun _ => false) := fun _ => (xorDot_zero r a).symm
  have := same_from_window h zeros initial t
  simp_all

/-- Once a periodic tail is eventually constant, it is constant from the
    beginning of that periodic tail, regardless of the decoder. -/
theorem periodic_latch {f : Nat → α} {h p t : Nat} (hp : 0 < p)
    (period : ∀ j, h ≤ j → f (j + p) = f j) {a : α}
    (latched : ∀ j, t ≤ j → f j = a) (j : Nat) (hj : h ≤ j) : f j = a := by
  have farther (k : Nat) : ∃ m, j + k ≤ m ∧ f m = f j := by
    induction k with
    | zero => exact ⟨j, by omega, rfl⟩
    | succ k ih =>
      obtain ⟨m, hm, eq⟩ := ih
      exact ⟨m + p, by omega, (period m (by omega)).trans eq⟩
  obtain ⟨m, hm, eq⟩ := farther t
  exact eq.symm.trans (latched m (by omega))

end ObservableRecurrence
