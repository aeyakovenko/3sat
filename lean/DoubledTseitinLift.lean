import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Abel

namespace DoubledTseitinLift

abbrev Bit := ZMod 2

structure Triple (E : Type*) where
  a : E
  b : E
  c : E

def Triple.total (t : Triple E) (x : E → Bit) := x t.a + x t.b + x t.c

def Base (row : V → Triple E) (charge : V → Bit) (x : E → Bit) :=
  ∀ v, (row v).total x = charge v

def Lift (row : V → Triple E) (charge : V → Bit) (y : E → Bit → Bit) :=
  ∀ v i j k, y (row v).a i + y (row v).b j + y (row v).c k = charge v + i + j + k

theorem lift_iff_base (row : V → Triple E) (charge : V → Bit) :
    (∃ y, Lift row charge y) ↔ ∃ x, Base row charge x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨fun e => y e 0, fun v => by simpa [Triple.total] using hy v 0 0 0⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun e i => x e + i, fun v i j k => ?_⟩
    simp only [← hx v, Triple.total, add_comm, add_left_comm]

/-- The representative of a pair can be chosen independently at every edge. -/
theorem representative_equations {row : V → Triple E} {charge : V → Bit}
    {y : E → Bit → Bit} (hy : Lift row charge y) (r : E → Bit) :
    Base row (fun v => charge v + (row v).total r) (fun e => y e (r e)) := by
  intro v
  simpa [Triple.total, add_assoc] using hy v (r (row v).a) (r (row v).b) (r (row v).c)

/-- For any copy choices the RHS measured relative to the chosen representatives
    equals its measured baseline plus the three relative copy bits. -/
theorem shifted_rhs (row : V → Triple E) (charge : V → Bit) (r : E → Bit) (v : V) (i j k : Bit) :
    charge v + (r (row v).a + i) + (r (row v).b + j) + (r (row v).c + k) =
      (charge v + (row v).total r) + i + j + k := by unfold Triple.total; abel

theorem representative_base_iff (row : V → Triple E) (charge : V → Bit) (r : E → Bit) :
    (∃ x, Base row (fun v => charge v + (row v).total r) x) ↔ ∃ x, Base row charge x := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun e => x e - r e, fun v => ?_⟩
    calc
      _ = (row v).total x - (row v).total r := by
        simp [Triple.total, sub_eq_add_neg, add_comm, add_left_comm]
      _ = charge v := by simp only [hx v, add_sub_cancel_right]
  · rintro ⟨x, hx⟩
    refine ⟨fun e => x e + r e, fun v => ?_⟩
    change (row v).total (fun e => x e + r e) = charge v + (row v).total r
    simp only [← hx v, Triple.total, add_comm, add_left_comm]

/- Oriented incidence over F₂; here subtraction and addition agree. The two
    endpoint functions allow parallel edges. The connected result applies to
    each connected component separately, with both vertex and edge types
    restricted to that component. -/
section Incidence

variable {V E : Type*} [DecidableEq V] [Fintype E]

private def packet (u v : V) (z : Bit) : V → Bit := Pi.single u z - Pi.single v z

def boundary (src dst : E → V) : (E → Bit) →+ (V → Bit) where
  toFun flow := ∑ e, packet (src e) (dst e) (flow e)
  map_zero' := by simp [packet]
  map_add' f g := by
    change (∑ e, packet (src e) (dst e) (f e + g e)) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [packet, Pi.single_add]
    abel

def EdgeStep (src dst : E → V) (u v : V) := ∃ e, src e = u ∧ dst e = v

private theorem packet_of_edge (src dst : E → V) (e : E) (z : Bit) :
    packet (src e) (dst e) z ∈ (boundary src dst).range := by
  classical
  refine ⟨Pi.single e z, ?_⟩
  change (∑ f, packet (src f) (dst f) ((Pi.single e z : E → Bit) f)) = _
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ ne; simp [ne, packet]
  · simp

/-- Flow may be routed along any undirected path of the underlying graph. -/
private theorem packet_of_path (src dst : E → V) {u v : V}
    (path : Relation.EqvGen (EdgeStep src dst) u v) (z : Bit) :
    packet u v z ∈ (boundary src dst).range := by
  induction path with
  | rel u v hedge =>
    obtain ⟨e, rfl, rfl⟩ := hedge
    exact packet_of_edge src dst e z
  | refl u => simp [packet]
  | symm u v _ ih => simpa [packet] using (boundary src dst).range.neg_mem ih
  | trans u v w _ _ ih₁ ih₂ =>
    simpa [packet] using (boundary src dst).range.add_mem ih₁ ih₂

/-- The oriented boundary really is the three-literal XOR on a loopless graph
    whose incident edge set at `v` is exactly the listed triple. -/
theorem boundary_at_cubic [DecidableEq E] (src dst : E → V) (v : V) (t : Triple E)
    (noLoops : ∀ e, src e ≠ dst e) (hab : t.a ≠ t.b) (hac : t.a ≠ t.c) (hbc : t.b ≠ t.c)
    (incident : Finset.univ.filter (fun e => src e = v ∨ dst e = v) = {t.a,t.b,t.c})
    (flow : E → Bit) : boundary src dst flow v = t.total flow := by
  change (∑ e, packet (src e) (dst e) (flow e)) v = _
  rw [Finset.sum_apply]
  have atEdge (e : E) : packet (src e) (dst e) (flow e) v =
      if src e = v ∨ dst e = v then flow e else 0 := by
    by_cases hs : src e = v
    · have hd : dst e ≠ v := fun eq => noLoops e (hs.trans eq.symm)
      simp [packet, hs, Ne.symm hd]
    · by_cases hd : dst e = v <;>
        simp [packet, hs, hd, Ne.symm hs, ZMod.neg_eq_self_mod_two]
  simp_rw [atEdge]
  rw [← Finset.sum_filter, incident]
  simp [Triple.total, hab, hac, hbc, add_assoc]

/-- For a finite connected component, a flow realizes the vertex charges
    exactly when the component has even total charge. -/
theorem connected_solvability [Fintype V] (src dst : E → V) (root : V)
    (connected : ∀ v, Relation.EqvGen (EdgeStep src dst) v root) (charge : V → Bit) :
    (∃ flow, boundary src dst flow = charge) ↔ ∑ v, charge v = 0 := by
  classical
  constructor
  · rintro ⟨flow, rfl⟩
    change (∑ v, (∑ e, packet (src e) (dst e) (flow e)) v) = 0
    simp_rw [Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    simp [packet, Pi.single_apply, Finset.sum_sub_distrib]
  · intro even
    have member := (boundary src dst).range.sum_mem (t := Finset.univ)
      (fun v _ => packet_of_path src dst (connected v) (charge v))
    have shrink : (∑ v, packet v root (charge v)) = charge := by
      funext u
      simp [Finset.sum_apply, packet, Pi.single_apply, Finset.sum_sub_distrib,
        Finset.sum_ite_irrel, even]
    rw [shrink] at member
    exact member

#print axioms lift_iff_base
#print axioms representative_base_iff
#print axioms boundary_at_cubic
#print axioms connected_solvability

end Incidence
end DoubledTseitinLift
