import Std

/-! Exact algebra of splitting logical occurrences into four-sheet relays. -/

namespace RelaySquareClones

def port (x a b : Bool) : Bool := !x || a || !b

def box (c a b z : Bool) : Bool :=
  port c a b && port a c z && port b z c && port z b a

def descent (s t : Bool) : Bool := s && !t

theorem square_equation (c a b z : Bool) :
    box c a b z = true ↔ (c && b) = (z && a) := by decide +revert

theorem link (v next w : Bool) :
    box v (!w) (!next) w = true ↔ v = true → next = true := by decide +revert

theorem equal_descent_filler (x y : Bool) : box x (!y) (!y) x = true := by decide +revert

theorem two_self_edges (x y : Bool) : box x (!y) (!x) y = true := by decide +revert

theorem closed_relays (n : Nat) (v w : Nat → Bool)
    (h : ∀ i < n, box (v i) (!(w i)) (!(v (i+1))) (w i) = true)
    (closed : v n = v 0) : ∀ i ≤ n, v i = v 0 := by
  have path (i d : Nat) (bound : i + d ≤ n) : v i = true → v (i+d) = true := by
    induction d with
    | zero => simp
    | succ d ih =>
      have step := (link _ _ _).mp (h (i+d) (by omega))
      exact fun hi => step (ih (by omega) hi)
  intro i hi
  have forward : v 0 = true → v i = true := by simpa using path 0 i (by omega)
  have back : v i = true → v 0 = true := by
    have add : i + (n-i) = n := by omega
    simpa [add, closed] using path i (n-i) (by omega)
  cases a : v 0 <;> cases b : v i <;> simp_all

/-- Arbitrary old constraints inspect the bits at their occurrence positions.
A cyclic link for each position implements exactly a single shared logical value. -/
theorem splitting_preserves_sat {V : Type} (len : V → Nat)
    (body : ((v : V) → Fin (len v) → Bool) → Prop) :
    (∃ s : V → Bool, body (fun v _ => s v)) ↔
    ∃ clone w : V → Nat → Bool,
      (∀ v, clone v (len v) = clone v 0) ∧
      (∀ v i, i < len v → box (clone v i) (!(w v i)) (!(clone v (i+1))) (w v i) = true) ∧
      body (fun v j => clone v j.val) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨fun v _ => s v, fun _ _ => false, fun _ => rfl,
      fun v _ _ => (link _ _ _).mpr (fun H => H), hs⟩
  · rintro ⟨clone, w, closes, links, hb⟩
    refine ⟨fun v => clone v 0, ?_⟩
    have agree : (fun (v : V) (j : Fin (len v)) => clone v j.val) =
        (fun v _ => clone v 0) := by
      funext v j
      exact closed_relays _ _ _ (links v) (closes v) j.val (Nat.le_of_lt j.isLt)
    rwa [agree] at hb

#print axioms splitting_preserves_sat
end RelaySquareClones
