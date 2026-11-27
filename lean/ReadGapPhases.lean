import Std

namespace ReadGapPhases

/-- Grid boundaries occur just before times sharing a residue. A previous touch at p
    and a read at r are split exactly when (p,r] contains such a boundary. -/
def crossing (w p r phase : Nat) : Prop :=
  ∃ t, p < t ∧ t ≤ r ∧ t % w = phase

/-- Enumerate the residues attained before the interval runs through one full period. -/
def phases (w p r : Nat) : List Nat :=
  (List.range (min w (r-p))).map fun i => (p+1+i) % w

theorem length_phases (w p r : Nat) :
    (phases w p r).length = min w (r-p) := by
  simp [phases]

theorem mem_phases_iff {w : Nat} (hw : 0 < w) (p r phase : Nat) :
    phase ∈ phases w p r ↔ crossing w p r phase := by
  simp only [phases, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, heq⟩
    have bound := (Nat.lt_min.mp hi).2
    exact ⟨p+1+i, by omega, by omega, heq⟩
  · rintro ⟨t, ht, hr, htphase⟩
    let i := t-(p+1)
    have ht' : t = p+1+i := by dsimp [i]; omega
    have di : i < r-p := by dsimp [i]; omega
    have rem := Nat.mod_le i w
    refine ⟨i%w, Nat.lt_min.mpr ⟨Nat.mod_lt i hw, by omega⟩, ?_⟩
    rw [Nat.add_mod_mod, ← ht', htphase]

theorem shifted_residue_injective {w i j : Nat} (base : Nat)
    (hi : i < w) (hj : j < w) (same : (base+i)%w = (base+j)%w) : i=j := by
  have hbase := Nat.mod_lt base (show w>0 by omega)
  have norm (k : Nat) (hk : k<w) : (base+k)%w =
      if base%w+k<w then base%w+k else base%w+k-w := by
    rw [← Nat.mod_add_mod base w k]
    split
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [norm i hi, norm j hj] at same
  split at same <;> split at same <;> omega

theorem nodup_phases (w p r : Nat) : (phases w p r).Nodup := by
  unfold phases List.Nodup
  apply List.pairwise_map.mpr
  have base : (List.range (min w (r-p))).Nodup := List.nodup_range
  refine base.imp_of_mem ?_
  intro a b ha hb ne heq
  exact ne (shifted_residue_injective (p+1)
    (Nat.lt_min.mp (List.mem_range.mp ha)).1 (Nat.lt_min.mp (List.mem_range.mp hb)).1 heq)

/-- Add one charge per crossing phase for every predecessor/read pair. -/
def totalCharges (w : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (p,r)::rest => (phases w p r).length + totalCharges w rest

theorem totalCharges_eq (w : Nat) (edges : List (Nat × Nat)) :
    totalCharges w edges = (edges.map fun e => min w (e.2-e.1)).sum := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨p,r⟩
    simp [totalCharges, length_phases, ih]

/-- A bag with one phase occurrence for each separated predecessor/read edge. -/
def chargeBag (w : Nat) (edges : List (Nat × Nat)) : List Nat :=
  edges.flatMap fun e => phases w e.1 e.2

theorem chargeBag_length (w : Nat) (edges : List (Nat × Nat)) :
    (chargeBag w edges).length = totalCharges w edges := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨p,r⟩
    simpa only [chargeBag, List.flatMap_cons, List.length_append, totalCharges] using
      congrArg (fun n => (phases w p r).length+n) ih

/-- Sum of the multiplicities of phases strictly below the limit. -/
private def mass (bag : List Nat) : Nat → Nat
  | 0 => 0
  | limit+1 => mass bag limit + bag.count limit

private theorem mass_cons (limit x : Nat) (bag : List Nat) :
    mass (x::bag) limit = mass bag limit + if x<limit then 1 else 0 := by
  induction limit with
  | zero => simp [mass]
  | succ n ih =>
    simp only [mass, ih, List.count_cons, beq_iff_eq]
    split <;> split <;> split <;> omega

private theorem mass_all (limit : Nat) (bag : List Nat) (bound : ∀ x ∈ bag, x<limit) :
    mass bag limit = bag.length := by
  induction bag with
  | nil =>
    induction limit with
    | zero => rfl
    | succ n ih => simp [mass, ih]
  | cons x xs ih =>
    have hx := bound x (by simp)
    have tail : ∀ y ∈ xs, y<limit := fun y hy => bound y (by simp [hy])
    simp [mass_cons, hx, ih tail]

private theorem mass_lower (limit c : Nat) (bag : List Nat)
    (low : ∀ j, j<limit → c ≤ bag.count j) : c*limit ≤ mass bag limit := by
  induction limit with
  | zero => simp [mass]
  | succ n ih =>
    have left := ih (fun j hj => low j (by omega))
    have right := low n (by omega)
    simp only [mass, Nat.mul_succ]
    omega

theorem exists_low_phase {w : Nat} (hw : 0<w) (edges : List (Nat × Nat)) :
    ∃ phase, phase<w ∧ (chargeBag w edges).count phase ≤ totalCharges w edges / w := by
  classical
  let bag := chargeBag w edges
  have bounds : ∀ j ∈ bag, j<w := by
    intro j h
    obtain ⟨e, _, occurs⟩ := List.mem_flatMap.mp h
    obtain ⟨t, _, _, ht⟩ := (mem_phases_iff hw _ _ _).mp occurs
    exact ht ▸ Nat.mod_lt t hw
  have full : mass bag w = totalCharges w edges := (mass_all w bag bounds).trans (chargeBag_length _ _)
  apply Classical.byContradiction
  intro none
  have low (j : Nat) (hj : j<w) : totalCharges w edges / w+1 ≤ bag.count j := by
    have h : ¬ (bag.count j ≤ totalCharges w edges / w) := fun h => none ⟨j,hj,h⟩
    omega
  have big := mass_lower w _ _ low
  have small := (Nat.div_lt_iff_lt_mul hw).mp
    (show totalCharges w edges / w < totalCharges w edges / w+1 by omega)
  omega

end ReadGapPhases
