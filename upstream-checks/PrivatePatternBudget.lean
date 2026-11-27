import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PrivatePatternBudget
open Finset

variable {V I : Type} [DecidableEq V] [DecidableEq I]
variable (x : I → V → Bool)

noncomputable def matching (w : Finset I) (s : Finset V) (p : V → Bool) : Finset I := by
  classical
  exact w.filter fun a => ∀ i ∈ s, x a i = p i

def robust (w : Finset I) (b : Nat) (s : Finset V) : Prop :=
  ∀ p, b < (matching x w s p).card

noncomputable def budget (v : Finset V) (w : Finset I) (b : Nat) : Finset (Finset V) := by
  classical
  exact v.powerset.filter (robust x w b)

def side (w : Finset I) (z : V) (c : Bool) : Finset I :=
  w.filter fun a => x a z = c

omit [DecidableEq V] [DecidableEq I] in
theorem matching_mono {u w : Finset I} (h : u ⊆ w) (s : Finset V) (p : V → Bool) :
    matching x u s p ⊆ matching x w s p := by
  classical
  exact filter_subset_filter _ h

omit [DecidableEq V] [DecidableEq I] in
theorem robust_mono {u w : Finset I} {s : Finset V} {b : Nat}
    (h : u ⊆ w) (r : robust x u b s) : robust x w b s :=
  fun p => lt_of_lt_of_le (r p) (card_le_card (matching_mono x h s p))

omit [DecidableEq V] [DecidableEq I] in
theorem robust_off_side {w : Finset I} {z : V} {c : Bool} {s : Finset V} {b : Nat}
    (r : robust x (side x w z c) b s) : z ∉ s := by
  classical
  intro hz
  have nonempty := card_pos.mp (lt_of_le_of_lt (Nat.zero_le b) (r (fun _ => !c)))
  obtain ⟨a, ha⟩ := nonempty
  simp only [matching, side, mem_filter] at ha
  have h := ha.2 z hz
  cases c <;> simp_all

omit [DecidableEq I] in
theorem robust_join {w : Finset I} {z : V} {s : Finset V} {b : Nat}
    (hl : robust x (side x w z false) b s) (hr : robust x (side x w z true) b s) :
    robust x w b (insert z s) := by
  classical
  intro p
  have incl : matching x (side x w z (p z)) s p ⊆ matching x w (insert z s) p := by
    intro a ha
    simp only [matching, side, mem_filter] at ha ⊢
    refine ⟨ha.1.1, ?_⟩
    intro i hi
    rcases mem_insert.mp hi with h | h
    · simpa [h] using ha.1.2
    · exact ha.2 _ h
  have child : robust x (side x w z (p z)) b s := by cases eq : p z <;> simp_all
  exact lt_of_lt_of_le (child p) (card_le_card incl)

omit [DecidableEq I] in
theorem budget_split (v : Finset V) (w : Finset I) (b : Nat) {z : V} (hz : z ∈ v) :
    (budget x v (side x w z false) b).card + (budget x v (side x w z true) b).card ≤
      (budget x v w b).card := by
  classical
  let L := budget x v (side x w z false) b
  let R := budget x v (side x w z true) b
  let both := L ∩ R
  let promoted := both.image (insert z)
  have fromL {s : Finset V} (hs : s ∈ L) := (Finset.mem_filter.mp hs).2
  have fromR {s : Finset V} (hs : s ∈ R) := (Finset.mem_filter.mp hs).2
  have off {s : Finset V} (hs : s ∈ L ∪ R) : z ∉ s := by
    rcases mem_union.mp hs with l | r
    · exact robust_off_side x (fromL l)
    · exact robust_off_side x (fromR r)
  have dis : Disjoint (L ∪ R) promoted := by
    apply disjoint_left.mpr
    intro s hu hi
    obtain ⟨t, _, rfl⟩ := mem_image.mp hi
    exact off hu (mem_insert_self _ _)
  have ij : Set.InjOn (insert z) (↑both : Set (Finset V)) := by
    intro a ha b' hb eq
    have hza := off (mem_union_left R (mem_inter.mp ha).1)
    have hzb := off (mem_union_left R (mem_inter.mp hb).1)
    simpa [hza,hzb] using congrArg (fun s : Finset V => s.erase z) eq
  have incl : (L ∪ R) ∪ promoted ⊆ budget x v w b := by
    intro s hs
    simp only [budget,mem_filter,mem_powerset]
    rcases mem_union.mp hs with hu | hp
    · rcases mem_union.mp hu with l | r
      · exact ⟨mem_powerset.mp (mem_filter.mp l).1, robust_mono x (filter_subset _ _) (fromL l)⟩
      · exact ⟨mem_powerset.mp (mem_filter.mp r).1, robust_mono x (filter_subset _ _) (fromR r)⟩
    · obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
      obtain ⟨l,r⟩ := mem_inter.mp ha
      exact ⟨insert_subset hz (mem_powerset.mp (mem_filter.mp l).1), robust_join x (fromL l) (fromR r)⟩
  have h := card_le_card incl
  rw [card_union_of_disjoint dis, show promoted.card = both.card from card_image_of_injOn ij] at h
  exact (card_union_add_card_inter L R) ▸ h


omit [DecidableEq V] [DecidableEq I] in
theorem side_partition (w : Finset I) (z : V) :
    (side x w z false).card + (side x w z true).card = w.card := by
  classical
  simpa [side] using (card_filter_add_card_filter_not (s := w) (fun a => x a z = false))

omit [DecidableEq V] in
theorem minority_cover (w : Finset I) (s : Finset V) (base : V → Bool) (b : Nat)
    (errors : ∀ i ∈ s, (side x w i (!(base i))).card ≤ b)
    (fails : (matching x w s base).card ≤ b) : w.card ≤ (s.card + 1)*b := by
  classical
  let E := s.biUnion (fun i => side x w i (!(base i)))
  have incl : w ⊆ matching x w s base ∪ E := by
    intro a ha
    by_cases h : ∀ i ∈ s, x a i = base i
    · exact mem_union_left E (mem_filter.mpr ⟨ha,h⟩)
    · simp only [not_forall] at h
      obtain ⟨i,hi,ne⟩ := h
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨i,hi,mem_filter.mpr ⟨ha,?_⟩⟩
      cases h₁ : x a i <;> cases h₂ : base i <;> simp_all
  have he : E.card ≤ s.card*b := by
    calc
      E.card ≤ ∑ i ∈ s, (side x w i (!(base i))).card := card_biUnion_le
      _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum errors
      _ = s.card * b := by simp
  calc
    w.card ≤ (matching x w s base ∪ E).card := card_le_card incl
    _ ≤ (matching x w s base).card + E.card := card_union_le _ _
    _ ≤ b + s.card*b := Nat.add_le_add fails he
    _ = _ := by simp [Nat.add_mul,Nat.add_comm]

/-- Each assignment must be rare on an actual support of bounded width. -/
def RareCover (v : Finset V) (u : Finset I) (k b : Nat) : Prop :=
  ∀ base : V → Bool, ∃ s ⊆ v, s.card ≤ k ∧ (matching x u s base).card ≤ b

omit [DecidableEq V] in
theorem split_exists (v : Finset V) (u w : Finset I) {k b : Nat}
    (hw : w ⊆ u) (cover : RareCover x v u k b)
    (large : (k+1)*b < w.card) :
    ∃ z ∈ v, b < (side x w z false).card ∧ b < (side x w z true).card := by
  classical
  by_contra! h
  let base := fun z => decide ((side x w z false).card ≤ b)
  obtain ⟨s, hs, size, rare⟩ := cover base
  have err (i) (hi : i ∈ s) : (side x w i (!(base i))).card ≤ b := by
    by_cases small : (side x w i false).card ≤ b
    · simp [base,small]
    · simpa [base,small] using h i (hs hi) (Nat.lt_of_not_ge small)
  have fail : (matching x w s base).card ≤ b :=
    le_trans (card_le_card (matching_mono x hw s base)) rare
  have c := minority_cover x w s base b err fail
  exact (Nat.not_lt_of_ge (le_trans c (Nat.mul_le_mul_right b (Nat.add_le_add_right size 1)))) large

omit [DecidableEq V] [DecidableEq I] in
theorem budget_nonempty (v : Finset V) (w : Finset I) {b : Nat} (small : b < w.card) :
    0 < (budget x v w b).card := by
  classical
  apply card_pos.mpr
  refine ⟨∅,?_⟩
  simp only [budget,mem_filter,mem_powerset,empty_subset,true_and]
  intro p
  simpa [matching] using small

theorem weighted_budget (v : Finset V) (u : Finset I) {k b : Nat}
    (cover : RareCover x v u k b) {w : Finset I} (hw : w ⊆ u) (big : b < w.card) :
    w.card ≤ (k+1)*b*(budget x v w b).card := by
  classical
  induction hsz : w.card using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rw [←hsz]
    by_cases small : w.card ≤ (k+1)*b
    · exact le_trans small (Nat.le_mul_of_pos_right _ (budget_nonempty x v w big))
    · obtain ⟨z,hz,l,r⟩ := split_exists x v u w hw cover (Nat.lt_of_not_ge small)
      have part := side_partition x w z
      have hl : side x w z false ⊆ w := filter_subset _ _
      have hr : side x w z true ⊆ w := filter_subset _ _
      have left := ih (side x w z false).card (by omega) (hl.trans hw) l rfl
      have right := ih (side x w z true).card (by omega) (hr.trans hw) r rfl
      rw [←part]
      apply le_trans (Nat.add_le_add left right)
      rw [←Nat.mul_add]
      exact Nat.mul_le_mul_left _ (budget_split x v w b hz)


/-- A full finite multiset theorem. Elements of I are occurrence IDs, so rows
    with equal Boolean values can occur with arbitrary integer multiplicity.
    The hypotheses give an actual forbidden word on each k-set, global UNSAT,
    and the simultaneous violation-count cap over the supplied row multiset. -/
theorem signed_complete_bound (v : Finset V) (u : Finset I) (k b : Nat) (hk : 0 < k)
    (forbid : Finset V → V → Bool)
    (unsat : ∀ a : V → Bool, ∃ s ⊆ v, s.card = k ∧ ∀ i ∈ s, a i = forbid s i)
    (cap : ∀ s ⊆ v, s.card = k → (matching x u s (forbid s)).card ≤ b) :
    u.card ≤ (k+1)*b * ∑ j ∈ range k, v.card.choose j := by
  classical
  have cover : RareCover x v u k b := by
    intro a
    obtain ⟨s,hs,hcard,matchA⟩ := unsat a
    refine ⟨s,hs,hcard.le,le_trans (card_le_card ?_) (cap s hs hcard)⟩
    intro i hi
    simp only [matching,mem_filter] at hi ⊢
    exact ⟨hi.1,fun t ht => (hi.2 t ht).trans (matchA t ht)⟩
  let short := (range k).biUnion (fun j => powersetCard j v)
  have inc : budget x v u b ⊆ short := by
    intro s hs
    obtain ⟨inV,rich⟩ := mem_filter.mp hs
    have sub := mem_powerset.mp inV
    have lt : s.card < k := by
      by_contra! big
      obtain ⟨t,ts,tk⟩ := exists_subset_card_eq big
      have bound := cap t (ts.trans sub) tk
      have more := rich (forbid t)
      have h : matching x u s (forbid t) ⊆ matching x u t (forbid t) := by
        intro a ha
        simp only [matching,mem_filter] at ha ⊢
        exact ⟨ha.1,fun j hj => ha.2 j (ts hj)⟩
      exact (Nat.not_lt_of_ge (le_trans (card_le_card h) bound)) more
    exact mem_biUnion.mpr ⟨s.card,mem_range.mpr lt,mem_powersetCard.mpr ⟨sub,rfl⟩⟩
  have rank : (budget x v u b).card ≤ ∑ j ∈ range k, v.card.choose j := by
    calc
      _ ≤ short.card := card_le_card inc
      _ ≤ ∑ j ∈ range k, (powersetCard j v).card := card_biUnion_le
      _ = _ := by simp
  by_cases high : b < u.card
  · exact le_trans (weighted_budget x v u cover (Finset.Subset.rfl) high)
      (Nat.mul_le_mul_left _ rank)
  · have one : 1 ≤ ∑ j ∈ range k, v.card.choose j := by
      simpa using (Finset.single_le_sum (fun i (_ : i ∈ range k) => Nat.zero_le (v.card.choose i))
        (mem_range.mpr hk))
    have prev : b ≤ (k+1)*b := by
      calc
        b = 1*b := by simp
        _ ≤ _ := Nat.mul_le_mul_right b (by omega)
    exact le_trans (le_trans (Nat.le_of_not_gt high) prev) (Nat.le_mul_of_pos_right _ one)


def PrivateWitness (v : Finset V) (k : Nat) (forbid : Finset V → V → Bool)
    (s : Finset V) (p : V → Bool) : Prop :=
  (∀ i ∈ s, p i = forbid s i) ∧
  ∀ t ⊆ v, t.card = k → t ≠ s → ¬∀ i ∈ t, p i = forbid t i

noncomputable def pivotal (v : Finset V) (k : Nat)
    (forbid : Finset V → V → Bool) : Finset (Finset V) := by
  classical
  exact (powersetCard k v).filter (fun s => ∃ p, PrivateWitness v k forbid s p)

/-- Cardinality of the actual set of supports with private assignments, for
    any complete unsatisfiable signed k-CNF on a finite set of variable names. -/
theorem pivotal_count (v : Finset V) (k : Nat) (hk : 0 < k)
    (forbid : Finset V → V → Bool)
    (unsat : ∀ a : V → Bool, ∃ s ⊆ v, s.card = k ∧ ∀ i ∈ s, a i = forbid s i) :
    (pivotal v k forbid).card ≤ (k+1) * ∑ j ∈ range k, v.card.choose j := by
  classical
  let P := pivotal v k forbid
  let choose := fun s : Finset V =>
    if h : ∃ p, PrivateWitness v k forbid s p then h.choose else fun _ => false
  have priv {s : Finset V} (hs : s ∈ P) : PrivateWitness v k forbid s (choose s) := by
    have h := (mem_filter.mp hs).2
    simpa [choose,h] using h.choose_spec
  have cap (s : Finset V) (hs : s ⊆ v) (hk' : s.card = k) :
      (matching choose P s (forbid s)).card ≤ 1 := by
    have inc : matching choose P s (forbid s) ⊆ {s} := by
      intro t ht
      obtain ⟨htP,matchT⟩ := mem_filter.mp ht
      apply mem_singleton.mpr
      by_contra ne
      exact (priv htP).2 s hs hk' (Ne.symm ne) matchT
    simpa using card_le_card inc
  simpa [P] using signed_complete_bound choose v P k 1 hk forbid unsat cap

end PrivatePatternBudget
