import Std

namespace PersistentForecastSearch

/-- A capped query made at threshold t is also tried on every longer input. -/
def prefixAny (hit : Nat → Bool) : Nat → Bool
  | 0 => hit 0
  | n+1 => prefixAny hit n || hit (n+1)

theorem prefixAny_iff (hit : Nat → Bool) (n : Nat) :
    prefixAny hit n = true ↔ ∃ t, t ≤ n ∧ hit t = true := by
  induction n with
  | zero =>
    simp [prefixAny]
  | succ n ih =>
    simp only [prefixAny, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨t, ht, hhit⟩ | hhit)
      · exact ⟨t, by omega, hhit⟩
      · exact ⟨n + 1, by omega, hhit⟩
    · rintro ⟨t, ht, hhit⟩
      by_cases now : t = n + 1
      · exact Or.inr (now ▸ hhit)
      · exact Or.inl ⟨t, by omega, hhit⟩

/-- Witness widths may exceed the threshold by any amount. -/
theorem quiet_tail {W : Type} (size : W → Nat) (hit : Nat → Bool)
    (zero : W → Prop)
    (sound : ∀ t, hit t = true → ∃ w, t ≤ size w ∧ zero w)
    (observed : ∀ w, zero w ↔ prefixAny hit (size w) = false) :
    (∀ t, hit t = false) ∧ ∀ w, zero w := by
  have none : ∀ t, hit t = false := by
    intro t
    cases hh : hit t with
    | false => rfl
    | true =>
      obtain ⟨w, hw, hz⟩ := sound t hh
      have yes := (prefixAny_iff hit (size w)).mpr ⟨t, hw, hh⟩
      have no := (observed w).mp hz
      simp [yes] at no
  refine ⟨none, fun w => (observed w).mpr ?_⟩
  cases hp : prefixAny hit (size w) with
  | false => rfl
  | true =>
    obtain ⟨t, _, yes⟩ := (prefixAny_iff hit (size w)).mp hp
    simp [none] at yes

/-- A sound proof of unboundedly many quiet widths is incompatible with a
    persistent eventually discovered signal. Search need have no time bound. -/
theorem unbounded_unreported {W : Type} (size : W → Nat)
    (found : Nat → Prop) (quiet : W → Prop)
    (sound : (∃ s, found s) → ∀ t, ∃ w, t ≤ size w ∧ quiet w)
    (late : ∀ s, found s → ∃ t, ∀ w, t ≤ size w → ¬ quiet w)
    (idle : (∀ s, ¬ found s) → ∀ w, quiet w) :
    (∀ s, ¬ found s) ∧ ∀ w, quiet w := by
  have none : ∀ s, ¬ found s := by
    intro s hs
    obtain ⟨t, ht⟩ := late s hs
    obtain ⟨w, hw, hz⟩ := sound ⟨s, hs⟩ t
    exact ht w hw hz
  exact ⟨none, idle none⟩

/-- A geometric budget can repeat every earlier query. Doubling is only
    required every two steps, accommodating dyadic rounding. -/
def total (budget : Nat → Nat) : Nat → Nat
  | 0 => budget 0
  | n+1 => total budget n + budget (n+1)

theorem total_le (budget : Nat → Nat)
    (increasing : ∀ n, budget n ≤ budget (n+1))
    (grows : ∀ n, 2 * budget n ≤ budget (n+2)) (n : Nat) :
    total budget n ≤ 4 * budget n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp only [total]; omega
    | 1 =>
      have h : budget 0 ≤ budget 1 := increasing 0
      change budget 0 + budget 1 ≤ 4 * budget 1
      omega
    | n+2 =>
      have hprev := ih n (by omega)
      have htwo := grows n
      have hone : budget (n+1) ≤ budget (n+2) := increasing (n+1)
      change total budget n + budget (n+1) + budget (n+2) ≤ 4 * budget (n+2)
      omega

/-- Between two consecutive square-exponent boundaries an entire pulse is
    observed. The ratio of endpoints controls the missing proportion. -/
theorem pulse_interval_ratio (j : Nat) :
    (2:Nat)^((j+1)*(j+1)) = 2^(j*j) * 2^(2*j+1) := by
  have h : (j+1)*(j+1) = j*j + (2*j+1) := by
    simp [Nat.add_mul, Nat.mul_add, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  rw [h, Nat.pow_add]

end PersistentForecastSearch
