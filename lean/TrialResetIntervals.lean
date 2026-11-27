import Std

namespace TrialResetIntervals

abbrev Choices := Nat → Option Nat

/-- The endpoint's candidate is retained precisely when it is live and
    agrees at every earlier phase in the closed window. -/
def gate (c : Choices) (lo m : Nat) : Option Nat :=
  if (List.range (m+1)).all (fun t => decide (t < lo) || c t == c m)
  then c m else none

theorem gateSome (c : Choices) (lo m k : Nat) (valid : lo ≤ m) :
    gate c lo m = some k ↔ ∀ t, lo ≤ t → t ≤ m → c t = some k := by
  constructor
  · intro h t lower upper
    unfold gate at h
    split at h
    next pass =>
      have inside := (List.all_eq_true.1 pass) t (List.mem_range.2 (by omega))
      have same : c t = c m := by simpa [Nat.not_lt_of_ge lower] using inside
      exact same.trans h
    next => contradiction
  · intro common
    have endpoint := common m valid (Nat.le_refl _)
    have pass : (List.range (m+1)).all (fun t => decide (t < lo) || c t == c m) = true := by
      apply List.all_eq_true.2
      intro t ht
      have upper := List.mem_range.1 ht
      by_cases before : t < lo
      · simp [before]
      · simp [before, common t (by omega) (by omega), endpoint]
    unfold gate
    rw [if_pos pass]
    exact endpoint

def reset (c : Choices) (j : Nat) : Prop :=
  c j = none ∨ c j ≠ c (j-1)

theorem resetKillsWindow (c : Choices) (lo j m : Nat)
    (inside : lo < j) (endAfter : j ≤ m) (fault : reset c j) : gate c lo m = none := by
  cases result : gate c lo m with
  | none => rfl
  | some k =>
    have common := (gateSome c lo m k (by omega)).1 result
    have atJ := common j (by omega) endAfter
    rcases fault with dead | changed
    · simp [dead] at atJ
    · exact False.elim (changed (atJ.trans (common (j-1) (by omega) (by omega)).symm))

/-- All integers in [j,2^j) still see both sides of the transition at j. -/
theorem resetKillsLogInterval (c : Choices) (j m : Nat)
    (positive : 0 < j) (start : j ≤ m) (finish : m < 2^j)
    (fault : reset c j) : gate c m.log2 m = none :=
  resetKillsWindow c _ j m ((Nat.log2_lt (by omega)).2 finish) start fault

def eventuallyLive (c : Choices) : Prop :=
  ∃ k t, ∀ m, t ≤ m → c m = some k

/-- If a tail has no resets, one candidate is live on that whole tail. -/
private theorem liveOfNoResets (c : Choices) (t : Nat)
    (quiet : ∀ j, t ≤ j → ¬ reset c j) : eventuallyLive c := by
  obtain ⟨k,hk⟩ : ∃ k, c t = some k := by
    cases ht : c t with
    | none => exact False.elim (quiet t (Nat.le_refl _) (Or.inl ht))
    | some k => exact ⟨k, rfl⟩
  refine ⟨k,t,?_⟩
  have tail (n : Nat) : c (t+n) = some k := by
    induction n with
    | zero => simpa using hk
    | succ n ih =>
      have same : c (t+(n+1)) = c (t+n) := by
        by_cases eq : c (t+(n+1)) = c (t+n)
        · exact eq
        · exact False.elim (quiet (t+(n+1)) (by omega) (Or.inr (by simpa using eq)))
      exact same.trans ih
  intro m hm
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hm
  exact tail n

theorem lateResets (c : Choices) (unstable : ¬ eventuallyLive c) (t : Nat) :
    ∃ j, t < j ∧ reset c j := by
  apply Classical.byContradiction
  intro absent
  apply unstable
  exact liveOfNoResets c (t+1) (fun j hj r => absent ⟨j, by omega, r⟩)

/-- Every candidate eventually disappears in the absence of a correct
    one, without any uniform bound on individual elimination times. -/
theorem failedCandidatesGiveIntervals (c : Choices)
    (eliminated : ∀ k, ∃ t, ∀ m, t ≤ m → c m ≠ some k) (t : Nat) :
    ∃ j, t < j ∧ ∀ m, j ≤ m → m < 2^j → gate c m.log2 m = none := by
  have unstable : ¬ eventuallyLive c := by
    rintro ⟨k,u,settled⟩
    obtain ⟨v,vanishes⟩ := eliminated k
    exact vanishes (max u v) (by omega) (settled _ (by omega))
  obtain ⟨j,hj,r⟩ := lateResets c unstable t
  exact ⟨j,hj,fun m a b => resetKillsLogInterval c j m (by omega) a b r⟩

theorem fixedEventuallyPasses (c : Choices) (k t : Nat)
    (fixed : ∀ m, t ≤ m → c m = some k) (m : Nat) (large : 2^t ≤ m) :
    gate c m.log2 m = some k := by
  apply (gateSome c m.log2 m k (Nat.log2_le_self _)).2
  have nz : m ≠ 0 := by have := Nat.two_pow_pos t; omega
  have past := (Nat.le_log2 nz).2 large
  exact fun i hi _ => fixed i (by omega)

/-- Even if successive gated values are allowed to depend on the phase,
    permanent nonempty gated output forces a single eventual live candidate. -/
theorem persistentGate (c : Choices) :
    (∃ t, ∀ m, t ≤ m → gate c m.log2 m ≠ none) ↔ eventuallyLive c := by
  constructor
  · rintro ⟨t,live⟩
    apply liveOfNoResets c (t+1)
    intro j hj fault
    exact live j (by omega) (resetKillsLogInterval c j j (by omega)
      (Nat.le_refl _) Nat.lt_two_pow_self fault)
  · rintro ⟨k,t,fixed⟩
    exact ⟨2^t, fun m hm hn => by simp [fixedEventuallyPasses c k t fixed m hm] at hn⟩

end TrialResetIntervals
