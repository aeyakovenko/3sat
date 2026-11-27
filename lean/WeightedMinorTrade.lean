import Std

namespace WeightedMinorTrade

/-- One update with c=C/B, d=D/K, λ=U/V and current exponent x/y.
    Numerators and denominators are retained without reducing them.
    The rate rule is stated for 0 < U ≤ V and positive denominators. -/
def step (C B D K U V : Nat) (xy : Nat × Nat) : Nat × Nat :=
  (2*C*V*D*xy.1, B*(2*(V-U)*D*xy.1 + 2*U*K*xy.1 + U*D*xy.2))

def iter (C B D K U V : Nat) : Nat → Nat × Nat
  | 0 => (D,K)
  | n+1 => step C B D K U V (iter C B D K U V n)

def belowOne (xy : Nat × Nat) : Bool := xy.1 < xy.2

theorem quarterWeight :
    (List.range 2).all (fun i => !belowOne (iter 11 10 11 10 1 4 i)) = true ∧
    belowOne (iter 11 10 11 10 1 4 2) = true := by decide

theorem halfWeight :
    (List.range 4).all (fun i => !belowOne (iter 47 40 47 40 1 2 i)) = true ∧
    belowOne (iter 47 40 47 40 1 2 4) = true := by decide

/-- d=e=1 and c=1+λ/2 leaves the exponent exactly one. -/
theorem linearEnvelope (u v : Nat) (h : u ≤ v) :
    let xy := step (2*v+u) (2*v) 1 1 u v (1,1)
    xy.1 = xy.2 := by
  simp only [step, Nat.mul_one]
  have equal : 2*(v-u) + 2*u + u = 2*v+u := by omega
  rw [equal]
  ac_rfl

theorem gatedClause (u v w y : Prop) :
    (∃ t : Prop, (u ∨ v ∨ t) ∧ (¬t ∨ w ∨ y)) ↔ u ∨ v ∨ w ∨ y := by
  constructor
  · rintro ⟨t, hu | hv | ht, tail⟩
    · exact Or.inl hu
    · exact Or.inr (Or.inl hv)
    · cases tail with
      | inl hn => exact False.elim (hn ht)
      | inr hwy => exact Or.inr (Or.inr hwy)
  · intro h
    cases h with
    | inl hu => exact ⟨False, Or.inl hu, Or.inl id⟩
    | inr h =>
      cases h with
      | inl hv => exact ⟨False, Or.inr (Or.inl hv), Or.inl id⟩
      | inr hwy => exact ⟨True, Or.inr (Or.inr True.intro), Or.inr hwy⟩

theorem unalteredGuard (a : Nat → Prop) (y : Prop) (m : Nat)
    (start : a 0) (links : ∀ i, i < m → a i → a (i+1)) (terminal : a m → ¬y) :
    ¬y := by
  apply terminal
  have advance : ∀ i, i ≤ m → a i := by
    intro i
    induction i with
    | zero => exact fun _ => start
    | succ i ih => exact fun h => links i (by omega) (ih (by omega))
  exact advance m (by omega)

theorem alteredGuard (k m : Nat) (hk : k < m) :
    ∃ a : Nat → Prop, a 0 ∧ ¬a m ∧
      (a k → ¬a (k+1)) ∧ (∀ i, i < m → i ≠ k → a i → a (i+1)) := by
  refine ⟨fun i => i ≤ k, by omega, by omega, by simp, ?_⟩
  intro i _ distinct prev
  omega

end WeightedMinorTrade
