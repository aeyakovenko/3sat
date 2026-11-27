import Std

namespace AddressOrders

/-- A tape head changes its position by at most one per step. -/
def UnitWalk (x : Nat → Int) : Prop :=
  ∀ t, x t ≤ x (t+1) + 1 ∧ x (t+1) ≤ x t + 1

private theorem rises_through (x : Nat → Int) (walk : UnitWalk x) (i n : Nat) (a : Int)
    (lo : x i ≤ a) (hi : a ≤ x (i+n)) :
    ∃ t, i ≤ t ∧ t ≤ i+n ∧ x t = a := by
  induction n with
  | zero => exact ⟨i, by omega, by omega, by simpa using Int.le_antisymm lo (by simpa using hi)⟩
  | succ n ih =>
    by_cases before : a ≤ x (i+n)
    · obtain ⟨t, ht, ht', hx⟩ := ih before
      exact ⟨t, ht, by omega, hx⟩
    · have step := (walk (i+n)).2
      have eqtime : i+n+1 = i+(n+1) := by omega
      rw [eqtime] at step
      exact ⟨i+(n+1), by omega, by omega, by omega⟩

theorem between_visits (x : Nat → Int) (walk : UnitWalk x) {i j : Nat} (order : i ≤ j)
    (a : Int) (between : (x i ≤ a ∧ a ≤ x j) ∨ (x j ≤ a ∧ a ≤ x i)) :
    ∃ t, i ≤ t ∧ t ≤ j ∧ x t = a := by
  have span : i + (j-i) = j := by omega
  rcases between with ⟨left,right⟩ | ⟨left,right⟩
  · have h := rises_through x walk i (j-i) a left (by rwa [span])
    rwa [span] at h
  · have reverseWalk : UnitWalk (fun t => -x t) := by
      intro t
      have h := walk t
      dsimp
      omega
    obtain ⟨t, ht, ht', hx⟩ :=
      rises_through (fun t => -x t) reverseWalk i (j-i) (-a) (by dsimp; omega)
        (by rw [span]; dsimp; omega)
    exact ⟨t, ht, by omega, by omega⟩

end AddressOrders
