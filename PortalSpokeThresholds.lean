import Std

namespace PortalSpokeThresholds

/-- Connectivity at a fixed weight cut is an equivalence relation.
    A supported spoke stays in its endpoint's component above its own key. -/
theorem endpoints_iff_portals {V : Type} (C : Nat → V → V → Prop)
    (sym : ∀ w u v, C w u v → C w v u)
    (trans : ∀ w u v z, C w u v → C w v z → C w u z)
    (mono : ∀ s t u v, s ≤ t → C s u v → C t u v)
    (u v p q : V) (a b : Nat) (hu : C a u p) (hv : C b v q) :
    C (max a b) u v ↔ C (max a b) p q := by
  let t := max a b
  have hup : C t u p := mono a t u p (Nat.le_max_left _ _) hu
  have hvq : C t v q := mono b t v q (Nat.le_max_right _ _) hv
  constructor
  · intro huv
    exact trans t p v q (trans t p u v (sym t u p hup) huv) hvq
  · intro hpq
    exact trans t u q v (trans t u p q hup hpq) (sym t v q hvq)

theorem bottleneck_or (threshold left right : Nat) :
    threshold ≤ max left right ↔ threshold ≤ left ∨ threshold ≤ right := by
  omega

end PortalSpokeThresholds
