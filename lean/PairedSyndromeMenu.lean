import Std

namespace PairedSyndromeMenu

abbrev Word (r : Nat) := BitVec r

/-- Pick the representative with pivot bit zero in the orbit {x,x xor d}. -/
def rep {r : Nat} (d : Word r) (p : Nat) (x : Word r) : Word r :=
  if x.getLsbD p then x ^^^ d else x

/-- Delete zero after partitioning the full vector space into pairs. -/
def block {r : Nat} (d a : Word r) : List (Word r) :=
  [a, a ^^^ d].filter (fun x => decide (x ≠ 0))

theorem hasPivot {r : Nat} (d : Word r) (ne : d ≠ 0) :
    ∃ p, p < r ∧ d.getLsbD p = true := by
  apply Classical.byContradiction
  intro none
  apply ne
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  cases hb : d.getLsbD p with
  | false => simp
  | true => exact False.elim (none ⟨p, hp, hb⟩)

theorem repClear {r : Nat} (d x : Word r) (p : Nat) (hd : d.getLsbD p = true) :
    (rep d p x).getLsbD p = false := by
  cases hx : x.getLsbD p <;> simp [rep, hx, hd]

private theorem memBlock {r : Nat} (d a x : Word r) :
    x ∈ block d a ↔ (x = a ∨ x = a ^^^ d) ∧ x ≠ 0 := by
  simp [block]

/-- The representatives with clear pivot partition exactly the nonzero labels. -/
theorem memberIff {r : Nat} (d a x : Word r) (p : Nat)
    (hd : d.getLsbD p = true) (ha : a.getLsbD p = false) :
    x ∈ block d a ↔ x ≠ 0 ∧ rep d p x = a := by
  rw [memBlock]
  constructor
  · rintro ⟨same, nz⟩
    refine ⟨nz, ?_⟩
    rcases same with rfl | rfl
    · simp [rep, ha]
    · simp [rep, hd, ha, BitVec.xor_assoc]
  · rintro ⟨nz, repr⟩
    refine ⟨?_, nz⟩
    cases h : x.getLsbD p with
    | false => exact Or.inl (by simpa [rep, h] using repr)
    | true =>
      have hxd : x ^^^ d = a := by simpa [rep, h] using repr
      exact Or.inr (by simp [← hxd, BitVec.xor_assoc])

/-- Physical coordinates have a copy index; equal labels in different copies
remain different coordinates. The unique block index is the copy and the representative. -/
theorem copiedMemberIff {r copies : Nat} (d a x : Word r) (p : Nat)
    (i j : Fin copies) (hd : d.getLsbD p = true) (ha : a.getLsbD p = false) :
    (j,x) ∈ (block d a).map (fun v => (i,v)) ↔ j=i ∧ x ≠ 0 ∧ rep d p x = a := by
  constructor
  · intro h
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp h
    cases eq
    exact ⟨rfl, (memberIff d a x p hd ha).mp hv⟩
  · rintro ⟨rfl, prop⟩
    exact List.mem_map.mpr ⟨x, (memberIff d a x p hd ha).mpr prop, rfl⟩

theorem zeroBlock {r : Nat} (d : Word r) (nz : d ≠ 0) : block d 0 = [d] := by
  have nz' : d ≠ 0#r := nz
  simp [block, nz']

theorem pairBlock {r : Nat} (d a : Word r) (p : Nat) (hd : d.getLsbD p = true)
    (ha : a.getLsbD p = false) (nz : a ≠ 0) : block d a = [a, a ^^^ d] := by
  have nz' : a ≠ 0#r := nz
  have diff : a ≠ d := fun h => by simp [h, hd] at ha
  simp [block, nz', diff]

/-- XOR of the labels whose physical coordinates currently carry a set bit. -/
def contribution {r : Nat} (on : Word r → Bool) : List (Word r) → Word r
  | [] => 0
  | a :: rest => (if on a then a else 0) ^^^ contribution on rest

theorem blockSum {r : Nat} (d a : Word r) (p : Nat) (hd : d.getLsbD p = true)
    (ha : a.getLsbD p = false) : contribution (fun _ => true) (block d a) = d := by
  have nz : d ≠ 0 := fun h => by simp [h] at hd
  by_cases h : a = 0
  · subst a
    rw [zeroBlock d nz]
    simp [contribution]
  · rw [pairBlock d a p hd ha h]
    simp [contribution, ← BitVec.xor_assoc]

private theorem xorShuffle {r : Nat} (a b c d : Word r) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [BitVec.xor_assoc a b, ← BitVec.xor_assoc b c d,
    BitVec.xor_comm b c, BitVec.xor_assoc c b d, ← BitVec.xor_assoc a c]

private theorem contributionAdd {r : Nat} (xs : List (Word r)) (f g : Word r → Bool) :
    contribution (fun x => f x ^^ g x) xs = contribution f xs ^^^ contribution g xs := by
  induction xs with
  | nil => simp [contribution]
  | cons x xs ih =>
    have label : (if f x ^^ g x then x else 0) =
        (if f x then x else 0) ^^^ (if g x then x else 0) := by
      cases hf : f x <;> cases hg : g x <;> simp
    simp only [contribution, label, ih, xorShuffle]

private theorem contributionOn {r : Nat} (xs : List (Word r)) (f g : Word r → Bool)
    (same : ∀ x ∈ xs, f x = g x) : contribution f xs = contribution g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [contribution, contribution, same x (by simp),
      ih (fun y hy => same y (List.mem_cons_of_mem _ hy))]

private theorem contributionFalse {r : Nat} (xs : List (Word r)) :
    contribution (fun _ => false) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [contribution, ih]

/-- Toggling is done on actual bits, including coordinates that already held one. -/
def repaired {r copies : Nat} (d : Word r) (p : Nat)
    (base fire : Fin copies → Word r → Bool) (i : Fin copies) (x : Word r) : Bool :=
  base i x ^^ fire i (rep d p x)

theorem repairBlock {r copies : Nat} (d a : Word r) (p : Nat) (i : Fin copies)
    (base fire : Fin copies → Word r → Bool) (hd : d.getLsbD p = true)
    (ha : a.getLsbD p = false) :
    contribution (repaired d p base fire i) (block d a) =
      contribution (base i) (block d a) ^^^ (if fire i a then d else 0) := by
  unfold repaired
  rw [contributionAdd]
  congr 1
  rw [contributionOn _ _ (fun _ => fire i a) (by
    intro x hx
    rw [((memberIff d a x p hd ha).mp hx).2])]
  cases h : fire i a with
  | false => exact contributionFalse _
  | true => exact blockSum d a p hd ha

/-- The seed (copy,clear-pivot representative) names one physical block. -/
def menuSum {r copies : Nat} (d : Word r) (base : Fin copies → Word r → Bool) :
    List (Fin copies × Word r) → Word r
  | [] => 0
  | (i,a)::rest => contribution (base i) (block d a) ^^^ menuSum d base rest

def parity {r copies : Nat} (fire : Fin copies → Word r → Bool) :
    List (Fin copies × Word r) → Bool
  | [] => false
  | (i,a)::rest => fire i a ^^ parity fire rest

/-- Sum over any menu of genuine block indices. For the full partition,
list each clear representative once for each copy; copiedMemberIff identifies
exactly one of those indices for every physical nonzero column. -/
theorem menuRepair {r copies : Nat} (d : Word r) (p : Nat)
    (base fire : Fin copies → Word r → Bool) (seeds : List (Fin copies × Word r))
    (hd : d.getLsbD p = true) (clear : ∀ z ∈ seeds, z.2.getLsbD p = false) :
    menuSum d (repaired d p base fire) seeds =
      menuSum d base seeds ^^^ (if parity fire seeds then d else 0) := by
  induction seeds with
  | nil => simp [menuSum, parity]
  | cons z zs ih =>
    obtain ⟨i,a⟩ := z
    have ha := clear (i,a) (by simp)
    have tail := ih (fun z hz => clear z (List.mem_cons_of_mem _ hz))
    simp only [menuSum, parity, repairBlock d a p i base fire hd ha, tail]
    rw [xorShuffle]
    have addFlag (u v : Bool) :
        (if u then d else 0) ^^^ (if v then d else 0) = (if u ^^ v then d else 0) := by
      cases u <;> cases v <;> simp
    rw [addFlag]

/-- All binary columns at width r, in numerical order. -/
def words (r : Nat) : List (Word r) := (List.range (2^r)).map (BitVec.ofNat r)

private theorem allWords {r : Nat} (x : Word r) : x ∈ words r := by
  exact List.mem_map.mpr ⟨x.toNat, List.mem_range.mpr x.isLt, by simp⟩

private theorem uniqueWords (r : Nat) : (words r).Nodup := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ List.nodup_range
  intro a b ha hb ne eq
  have vals := congrArg BitVec.toNat eq
  have ha' := List.mem_range.mp ha
  have hb' := List.mem_range.mp hb
  exact ne (by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using vals)

private theorem countInside {α : Type} [DecidableEq α] {xs pool : List α}
    (unique : xs.Nodup) (inside : ∀ x ∈ xs, x ∈ pool) : xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp unique
    have found := inside x (by simp)
    have pos := List.length_pos_of_mem found
    have smaller := ih tail (pool := pool.erase x) (by
      intro y hy
      have ne : y ≠ x := fun eq => fresh (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (inside y (by simp [hy])))
    rw [List.length_erase_of_mem found] at smaller
    simp
    omega

def side (r p : Nat) (b : Bool) : List (Word r) :=
  (words r).filter (fun v => v.getLsbD p == b)

private theorem sideInject {r : Nat} (d : Word r) (p : Nat) (b : Bool)
    (hd : d.getLsbD p = true) : (side r p b).length ≤ (side r p (!b)).length := by
  let src := side r p b
  let flip := fun x : Word r => x ^^^ d
  have nd : (src.map flip).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ (List.Pairwise.filter _ (uniqueWords r))
    intro x y ne eq
    exact ne ((BitVec.xor_left_inj d).mp eq)
  have le := countInside (pool := side r p (!b)) nd (by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, hb⟩ := List.mem_filter.mp hv
    have val : v.getLsbD p = b := by simpa using hb
    apply List.mem_filter.mpr
    exact ⟨allWords _, by simp [flip, val, hd]⟩)
  simpa [src] using le

/-- Xoring with d bijects the two halves, so there are exactly 2^n
clear-pivot representatives when the ambient width is n+1. -/
theorem labelCount (n : Nat) (d : Word (n+1)) (p : Nat) (hd : d.getLsbD p = true) :
    (side (n+1) p false).length = 2^n := by
  have f := sideInject d p false hd
  have t := sideInject d p true hd
  have total := (List.filter_append_perm (fun x : Word (n+1) => x.getLsbD p) (words (n+1))).length_eq
  simp only [List.length_append] at total
  have lengthWords : (words (n+1)).length = 2^n * 2 := by simp [words, Nat.pow_succ]
  simp [side] at f t ⊢
  rw [lengthWords] at total
  omega

/-- Duplicate the menu for independent physical copies. -/
def copyLabels {r : Nat} (ids : List I) (labels : List (Word r)) : List (I × Word r) :=
  ids.flatMap (fun i => labels.map (fun a => (i,a)))

private theorem lengthCopies {r : Nat} (ids : List I) (labels : List (Word r)) :
    (copyLabels ids labels).length = ids.length * labels.length := by
  induction ids with
  | nil => simp [copyLabels]
  | cons i ids ih => simpa [copyLabels, Nat.succ_mul, Nat.add_comm] using ih

theorem fullMenuLength (n copies : Nat) (d : Word (n+1)) (p : Nat)
    (hd : d.getLsbD p = true) :
    (copyLabels (List.finRange copies) (side (n+1) p false)).length = copies * 2^n := by
  rw [lengthCopies, labelCount n d p hd, List.length_finRange]

private theorem memFinRange {copies : Nat} (i : Fin copies) : i ∈ List.finRange copies := by
  apply List.mem_iff_getElem.mpr
  refine ⟨i.val, by simp, ?_⟩
  apply Fin.ext
  simp [List.getElem_finRange]

private theorem copiedLabelMem {r : Nat} (ids : List I) (labels : List (Word r))
    (i : I) (a : Word r) : (i,a) ∈ copyLabels ids labels ↔ i ∈ ids ∧ a ∈ labels := by
  constructor
  · intro h
    obtain ⟨j,hj,h⟩ := List.mem_flatMap.mp h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    cases eq
    exact ⟨hj,hb⟩
  · rintro ⟨hi,ha⟩
    exact List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨a,ha,rfl⟩⟩

private theorem clearOfMem {r p : Nat} {a : Word r} (h : a ∈ side r p false) :
    a.getLsbD p = false := by simpa using (List.mem_filter.mp h).2

/-- In the computed full menu every nonzero physical coordinate belongs to
one block, and a second containing index equals that block's index. -/
theorem fullPartition {r copies : Nat} (d x : Word r) (p : Nat) (i : Fin copies)
    (hd : d.getLsbD p = true) (nx : x ≠ 0) :
    let all := copyLabels (List.finRange copies) (side r p false)
    let cols := fun (z : Fin copies × Word r) => (block d z.2).map (fun v => (z.1,v))
    ∃ z ∈ all, (i,x) ∈ cols z ∧ ∀ w ∈ all, (i,x) ∈ cols w → w = z := by
  dsimp only
  let a := rep d p x
  have ca : a.getLsbD p = false := repClear d x p hd
  have ina : a ∈ side r p false := List.mem_filter.mpr ⟨allWords a, by simp [ca]⟩
  refine ⟨(i,a), (copiedLabelMem _ _ _ _).mpr ⟨memFinRange i, ina⟩,
    (copiedMemberIff d a x p i i hd ca).mpr ⟨rfl, nx, rfl⟩, ?_⟩
  rintro ⟨j,b⟩ hin hx
  have cb := clearOfMem ((copiedLabelMem _ _ _ _).mp hin).2
  obtain ⟨same, _, eq⟩ := (copiedMemberIff d b x p j i hd cb).mp hx
  exact Prod.ext same.symm eq.symm

/-- The parity identity with no abstract permutation or cover assumption. -/
theorem fullMenuRepair {r copies : Nat} (d : Word r) (p : Nat) (hd : d.getLsbD p = true)
    (base fire : Fin copies → Word r → Bool) :
    let all := copyLabels (List.finRange copies) (side r p false)
    menuSum d (repaired d p base fire) all =
      menuSum d base all ^^^ (if parity fire all then d else 0) := by
  apply menuRepair _ _ _ _ _ hd
  rintro ⟨i,a⟩ hin
  exact clearOfMem ((copiedLabelMem _ _ _ _).mp hin).2

end PairedSyndromeMenu
