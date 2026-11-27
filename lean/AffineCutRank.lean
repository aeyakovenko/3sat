import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset

namespace AffineCutRank

abbrev Bit := ZMod 2

/-- Each factor is either the constant 1 or one of the common feature bits. -/
abbrev Word (I : Type) (d : Nat) := Fin d → Option I

def factor (x : I → Bit) : Option I → Bit
  | none => 1
  | some i => x i

def monomial {d : Nat} (x : I → Bit) (w : Word I d) : Bit :=
  ∏ i, factor x (w i)

def expand [Fintype I] {d : Nat} (c : Word I d → Bit) (x : I → Bit) : Bit :=
  ∑ w, monomial x w * c w

def affine [Fintype I] (a : Option I → Bit) (x : I → Bit) : Bit :=
  ∑ i, factor x i * a i

def complement (a : Option I → Bit) (i : Option I) : Bit :=
  (if i.isNone then 1 else 0) - a i

theorem affine_complement [Fintype I] (a : Option I → Bit) (x : I → Bit) :
    affine (complement a) x = 1 - affine a x := by
  simp only [affine, complement, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Fintype.sum_option]
  simp [factor]

def prepend {d : Nat} (a : Option I → Bit) (c : Word I d → Bit)
    (w : Word I (d+1)) : Bit := a (w 0) * c (fun j => w j.succ)

theorem expand_prepend [Fintype I] (a : Option I → Bit) (c : Word I d → Bit) (x : I → Bit) :
    expand (prepend a c) x = affine a x * expand c x := by
  unfold expand
  rw [← (Fin.consEquiv (fun _ : Fin (d+1) => Option I)).sum_comp
    (fun w => monomial x w * prepend a c w), Fintype.sum_prod_type]
  simp only [monomial, Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero,
    Fin.cons_succ, prepend, affine, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem expand_add [Fintype I] (c e : Word I d → Bit) (x : I → Bit) :
    expand (fun w => c w + e w) x = expand c x + expand e x := by
  simp [expand, mul_add, Finset.sum_add_distrib]

/-- The query and a free header can each select a different tree. Each test
takes an arbitrary affine form on the shared preprocessing bits. -/
inductive Tree (I : Type) : Nat → Type where
  | leaf (answer : Bit) : Tree I 0
  | test (a : Option I → Bit) (low high : Tree I d) : Tree I (d+1)

def Tree.eval [Fintype I] (x : I → Bit) : Tree I d → Bit
  | .leaf v => v
  | .test a l r => if affine a x = 0 then l.eval x else r.eval x

def Tree.coefficients : Tree I d → (Word I d → Bit)
  | .leaf v => fun _ => v
  | .test a l r => fun w =>
    prepend (complement a) l.coefficients w + prepend a r.coefficients w

/-- Every column uses the same ordered degree-at-most-d monomials, even when
the later tests are selected by the preceding answers. -/
theorem shared_expansion [Fintype I] (x : I → Bit) (t : Tree I d) :
    expand t.coefficients x = t.eval x := by
  induction t with
  | leaf v => simp [Tree.coefficients, Tree.eval, expand, monomial]
  | test a l r hl hr =>
    simp only [Tree.coefficients, expand_add, expand_prepend, affine_complement, hl, hr, Tree.eval]
    have bits : ∀ b : Bit, b = 0 ∨ b = 1 := by decide
    rcases bits (affine a x) with h | h <;> simp [h]

/-- A short branch can always be extended by a redundant test. -/
def Tree.pad (t : Tree I d) : Tree I (d+1) := .test (fun _ => 0) t t

theorem pad_eval [Fintype I] (t : Tree I d) (x : I → Bit) :
    t.pad.eval x = t.eval x := by simp [Tree.pad, Tree.eval]

/-- The features can be arbitrary functions of the data row. Its header is
another arbitrary function of the row, fixed across the query columns. -/
def response [Fintype I] (feature : X → I → Bit) (header : X → H)
    (trees : H → Y → Tree I d) : Matrix X Y Bit :=
  fun x y => (trees (header x) y).eval (feature x)

theorem response_rank [Fintype I] [Fintype H] [Fintype Y]
    (feature : X → I → Bit) (header : X → H) (trees : H → Y → Tree I d) :
    (response feature header trees).rank ≤ Fintype.card H * (Fintype.card I + 1) ^ d := by
  classical
  let left : Matrix X (H × Word I d) Bit :=
    fun x z => if z.1 = header x then monomial (feature x) z.2 else 0
  let right : Matrix (H × Word I d) Y Bit := fun z y => (trees z.1 y).coefficients z.2
  have factorization : left * right = response feature header trees := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simpa [left, right, ite_mul, Finset.sum_ite_irrel, response, expand] using
      shared_expansion (feature x) (trees (header x) y)
  rw [← factorization]
  have bound := (Matrix.rank_mul_le_left left right).trans (Matrix.rank_le_card_width left)
  simpa [Word, Fintype.card_prod, Fintype.card_fun, Fintype.card_option] using bound

/-- Different completed paths may all have valid layout fields on one database
row. Their row masks may overlap, and need not be Boolean indicators of a
partition. The path simulation itself is allowed to choose zero as its output. -/
def weightedResponse [Fintype I] [Fintype H] (feature : X → I → Bit)
    (mask : H → X → Bit) (trees : H → Y → Tree I d) : Matrix X Y Bit :=
  fun x y => ∑ h, mask h x * (trees h y).eval (feature x)

theorem weighted_response_rank [Fintype I] [Fintype H] [Fintype Y]
    (feature : X → I → Bit) (mask : H → X → Bit) (trees : H → Y → Tree I d) :
    (weightedResponse feature mask trees).rank ≤ Fintype.card H * (Fintype.card I + 1) ^ d := by
  classical
  let left : Matrix X (H × Word I d) Bit :=
    fun x z => mask z.1 x * monomial (feature x) z.2
  let right : Matrix (H × Word I d) Y Bit := fun z y => (trees z.1 y).coefficients z.2
  have factorization : left * right = weightedResponse feature mask trees := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h _
    change (∑ w, (mask h x * monomial (feature x) w) * (trees h y).coefficients w) = _
    rw [← shared_expansion (feature x) (trees h y)]
    simp only [expand, Finset.mul_sum, mul_assoc]
  rw [← factorization]
  have bound := (Matrix.rank_mul_le_left left right).trans (Matrix.rank_le_card_width left)
  simpa [Word, Fintype.card_fun] using bound

/-- The equality claim need only hold on the specified rows and matching column
set. This directly applies to row masks of the layouts of alternative paths. -/
theorem weighted_identity_minor [Fintype I] [Fintype H] [DecidableEq X]
    (feature : X → I → Bit) (mask : H → X → Bit) (trees : H → X → Tree I d)
    (easy : Finset X) (correct : ∀ x ∈ easy, ∀ y ∈ easy,
      weightedResponse feature mask trees x y = if x = y then 1 else 0) :
    easy.card ≤ Fintype.card H * (Fintype.card I + 1) ^ d := by
  classical
  let f : easy → I → Bit := fun x => feature x.val
  let masks : H → easy → Bit := fun h x => mask h x.val
  let ts : H → easy → Tree I d := fun h y => trees h y.val
  have identity : weightedResponse f masks ts = 1 := by
    ext x y
    simpa only [Matrix.one_apply, Subtype.ext_iff, weightedResponse, f, masks, ts] using correct x.val x.property y.val y.property
  have bound := weighted_response_rank f masks ts
  rw [identity, Matrix.rank_one] at bound
  simpa using bound

/-- All 2^k columns of k-bit equality are independent over the actual test field. -/
theorem equality_requires [Fintype I] [Fintype H] {k d : Nat}
    (feature : (Fin k → Bool) → I → Bit) (header : (Fin k → Bool) → H)
    (trees : H → (Fin k → Bool) → Tree I d)
    (correct : ∀ x y, (trees (header x) y).eval (feature x) = if x = y then 1 else 0) :
    2 ^ k ≤ Fintype.card H * (Fintype.card I + 1) ^ d := by
  have identity : response feature header trees = 1 := by
    ext x y
    exact (correct x y).trans Matrix.one_apply.symm
  have bound := response_rank feature header trees
  rw [identity, Matrix.rank_one] at bound
  simpa [Fintype.card_fun] using bound

/-- Hitting the cutoff returns zero. Thus, when the full relation is equality,
only a query's successful diagonal path needs to be short to survive the cutoff. -/
inductive RawTree (I : Type) where
  | leaf (answer : Bit)
  | test (a : Option I → Bit) (low high : RawTree I)

def RawTree.run [Fintype I] (x : I → Bit) : RawTree I → Bit × Nat
  | .leaf v => (v, 0)
  | .test a l r =>
    let u := if affine a x = 0 then l.run x else r.run x
    (u.1, u.2 + 1)

def Tree.const (v : Bit) : (d : Nat) → Tree I d
  | 0 => .leaf v
  | d+1 => (Tree.const v d).pad

theorem const_eval [Fintype I] (v : Bit) (d : Nat) (x : I → Bit) :
    (Tree.const v d).eval x = v := by
  induction d with
  | zero => rfl
  | succ d ih => simpa only [Tree.const, pad_eval] using ih

def RawTree.cut : (d : Nat) → RawTree I → Tree I d
  | d, .leaf v => Tree.const v d
  | 0, .test _ _ _ => .leaf 0
  | d+1, .test a l r => .test a (l.cut d) (r.cut d)

theorem cut_semantics [Fintype I] (t : RawTree I) (x : I → Bit) (d : Nat) :
    (t.cut d).eval x = if (t.run x).2 ≤ d then (t.run x).1 else 0 := by
  induction t generalizing d with
  | leaf v => simp [RawTree.run, RawTree.cut, const_eval]
  | test a l r hl hr =>
    cases d with
    | zero => simp [RawTree.cut, Tree.eval, RawTree.run]
    | succ d =>
      by_cases h : affine a x = 0 <;>
        simp [RawTree.cut, Tree.eval, RawTree.run, h, hl, hr]

/-- Any finite set of cheap successful diagonals is small, even when all
off-diagonal runtimes and all other diagonal runtimes are unbounded by d.
The features and the header may be arbitrary preprocessing of the row. -/
theorem cheap_diagonals [Fintype I] [Fintype H] {X : Type} [DecidableEq X]
    (feature : X → I → Bit) (header : X → H) (trees : H → X → RawTree I)
    (correct : ∀ x y, ((trees (header x) y).run (feature x)).1 = if x = y then 1 else 0)
    (cheap : Finset X) (bound : ∀ x ∈ cheap, ((trees (header x) x).run (feature x)).2 ≤ d) :
    cheap.card ≤ Fintype.card H * (Fintype.card I + 1) ^ d := by
  classical
  let f : (x : cheap) → I → Bit := fun x => feature x.val
  let h : cheap → H := fun x => header x.val
  let qs : H → cheap → Tree I d := fun j y => (trees j y.val).cut d
  have identity : response f h qs = 1 := by
    ext x y
    simp only [response, f, h, qs, cut_semantics, Matrix.one_apply]
    by_cases same : x = y
    · subst y
      simp [correct, bound x.val x.property]
    · have ne : x.val ≠ y.val := fun he => same (Subtype.ext he)
      simp [correct, same, ne]
  have limits := response_rank f h qs
  rw [identity, Matrix.rank_one] at limits
  simpa using limits

/-- The squarefree support forgets constant factors, order and repetition. -/
def used [DecidableEq I] (w : Word I d) : Finset I :=
  Finset.univ.biUnion (fun j => (w j).toFinset)

private theorem used_card [DecidableEq I] (w : Word I d) : (used w).card ≤ d := by
  have one (j : Fin d) : (w j).toFinset.card ≤ 1 := by cases w j <;> simp
  simpa [used] using Finset.card_biUnion_le_card_mul Finset.univ
    (fun j => (w j).toFinset) 1 (fun j _ => one j)

theorem squarefree_monomial [DecidableEq I] (x : I → Bit) (w : Word I d) :
    monomial x w = ∏ i ∈ used w, x i := by
  classical
  have zero : monomial x w = 0 ↔ (∏ i ∈ used w, x i) = 0 := by
    simp only [monomial, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      cases e : w j with
      | none => simp [e, factor] at hj
      | some i =>
        refine ⟨i, Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩, ?_⟩
        · simp [e]
        · simpa [factor, e] using hj
    · rintro ⟨i, hi, hx⟩
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
      change i ∈ (w j).toFinset at hj
      cases e : w j with
      | none => simp [e] at hj
      | some i' =>
        have same : i = i' := by simpa [e] using hj
        exact ⟨j, by simpa [factor, e, ←same] using hx⟩
  have bits : ∀ b : Bit, b = 0 ∨ b = 1 := by decide
  rcases bits (monomial x w) with h | h
  · exact h.trans (zero.mp h).symm
  · rcases bits (∏ i ∈ used w, x i) with p | p
    · exact (zero.mpr p).trans p.symm
    · exact h.trans p.symm

abbrev Small (I : Type) (d : Nat) := {s : Finset I // s.card ≤ d}

def supportKey [DecidableEq I] (w : Word I d) : Small I d := ⟨used w, used_card w⟩

def collected [Fintype I] [DecidableEq I] (c : Word I d → Bit) (s : Small I d) : Bit :=
  ∑ w, if supportKey w = s then c w else 0

theorem squarefree_expansion [Fintype I] [DecidableEq I] (c : Word I d → Bit) (x : I → Bit) :
    (∑ s : Small I d, (∏ i ∈ s.val, x i) * collected c s) = expand c x := by
  classical
  simp only [collected, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  unfold expand
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_ite_eq]
  simp [supportKey, squarefree_monomial]

/-- Partition small supports by cardinality, including sizes beyond |I| with
zero binomial coefficient. -/
theorem number_of_small_supports [Fintype I] (d : Nat) :
    Fintype.card (Small I d) =
      ∑ j ∈ Finset.range (d+1), (Fintype.card I).choose j := by
  let split : Small I d ≃ ((j : Fin (d+1)) × {s : Finset I // s.card = j.val}) :=
    { toFun := fun s => ⟨⟨s.val.card, Nat.lt_succ_of_le s.property⟩, ⟨s.val, rfl⟩⟩
      invFun := fun p => ⟨p.2.val, by rw [p.2.property]; exact Nat.le_of_lt_succ p.1.isLt⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨j, hj⟩, s, eq⟩
        change s.card = j at eq
        subst j
        rfl }
  rw [Fintype.card_congr split, Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fin.sum_univ_eq_sum_range]

/-- Exact dimension ceiling for arbitrary overlapping row masks. -/
theorem weighted_squarefree_rank [Fintype I] [Fintype H] [Fintype Y]
    (feature : X → I → Bit) (mask : H → X → Bit) (trees : H → Y → Tree I d) :
    (weightedResponse feature mask trees).rank ≤ Fintype.card H *
      ∑ j ∈ Finset.range (d+1), (Fintype.card I).choose j := by
  classical
  let left : Matrix X (H × Small I d) Bit :=
    fun x z => mask z.1 x * ∏ i ∈ z.2.val, feature x i
  let right : Matrix (H × Small I d) Y Bit := fun z y => collected (trees z.1 y).coefficients z.2
  have factorization : left * right = weightedResponse feature mask trees := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro h _
    change (∑ s : Small I d, (mask h x * ∏ i ∈ s.val, feature x i) *
      collected (trees h y).coefficients s) = mask h x * _
    rw [← shared_expansion (feature x) (trees h y), ← squarefree_expansion]
    simp only [Finset.mul_sum, mul_assoc]
  rw [← factorization]
  have bound := (Matrix.rank_mul_le_left left right).trans (Matrix.rank_le_card_width left)
  simpa only [Fintype.card_prod, number_of_small_supports] using bound

theorem weighted_squarefree_identity_minor [Fintype I] [Fintype H] [DecidableEq X]
    (feature : X → I → Bit) (mask : H → X → Bit) (trees : H → X → Tree I d)
    (easy : Finset X) (correct : ∀ x ∈ easy, ∀ y ∈ easy,
      weightedResponse feature mask trees x y = if x = y then 1 else 0) :
    easy.card ≤ Fintype.card H * ∑ j ∈ Finset.range (d+1), (Fintype.card I).choose j := by
  classical
  let f : easy → I → Bit := fun x => feature x.val
  let masks : H → easy → Bit := fun h x => mask h x.val
  let ts : H → easy → Tree I d := fun h y => trees h y.val
  have identity : weightedResponse f masks ts = 1 := by
    ext x y
    simpa only [Matrix.one_apply, Subtype.ext_iff, weightedResponse, f, masks, ts] using
      correct x.val x.property y.val y.property
  have bound := weighted_squarefree_rank f masks ts
  rw [identity, Matrix.rank_one] at bound
  simpa using bound

/-- Pick one squarefree support of permitted size independently in each block.
No independence is required of the feature values as functions of the row. -/
abbrev BlockTuple {B : Type} (I : B → Type) (a : B → Nat) :=
  (j : B) → Small (I j) (a j)

def blockMonomial {B : Type} [Fintype B] {I : B → Type} {a : B → Nat}
    (features : (j : B) → X → I j → Bit) (x : X) (u : BlockTuple I a) : Bit :=
  ∏ j, ∏ i ∈ (u j).val, features j x i

theorem block_tuple_count {B : Type} [Fintype B] [DecidableEq B] (I : B → Type)
    [∀ j, Fintype (I j)] (a : B → Nat) :
    Fintype.card (BlockTuple I a) =
      ∏ j, ∑ n ∈ Finset.range (a j + 1), (Fintype.card (I j)).choose n := by
  rw [Fintype.card_pi]
  simp only [number_of_small_supports]

/-- Along a fixed accepting path, each block's conjunction of affine tests can
be given as its own depth-bounded decision tree. Multiplying their outputs
already has the common product-basis representation used by the rank bound. -/
theorem product_of_block_trees {B : Type} [Fintype B] [DecidableEq B]
    (I : B → Type) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] (a : B → Nat)
    (features : (j : B) → X → I j → Bit) (x : X)
    (ts : (j : B) → Tree (I j) (a j)) :
    (∏ j, (ts j).eval (features j x)) = ∑ u : BlockTuple I a,
      blockMonomial features x u * ∏ j, collected (ts j).coefficients (u j) := by
  calc
    _ = ∏ j, ∑ s : Small (I j) (a j),
        (∏ i ∈ s.val, features j x i) * collected (ts j).coefficients s := by
      apply Finset.prod_congr rfl
      intro j _
      rw [squarefree_expansion, shared_expansion]
    _ = _ := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp only [blockMonomial, Finset.prod_mul_distrib]

/-- Each layout type may have its own blocks, feature spaces, preprocessing,
degree caps and query coefficients. Overlapping row masks multiply its shared
basis functions. Factoring through the disjoint union of the type-specific
product bases bounds the rank by their total size. -/
theorem type_block_response_rank [Fintype H] [Fintype Y]
    (B : H → Type) [∀ h, Fintype (B h)] [∀ h, DecidableEq (B h)]
    (I : (h : H) → B h → Type) [∀ h j, Fintype (I h j)] (a : (h : H) → B h → Nat)
    (features : (h : H) → (j : B h) → X → I h j → Bit) (mask : H → X → Bit)
    (c : (h : H) → Y → BlockTuple (I h) (a h) → Bit) (A : Matrix X Y Bit)
    (rep : ∀ x y, A x y = ∑ h, mask h x *
      ∑ u, blockMonomial (features h) x u * c h y u) :
    A.rank ≤ ∑ h, ∏ j, ∑ n ∈ Finset.range (a h j + 1), (Fintype.card (I h j)).choose n := by
  classical
  let Common := (h : H) × BlockTuple (I h) (a h)
  let left : Matrix X Common Bit :=
    fun x s => mask s.1 x * blockMonomial (features s.1) x s.2
  let right : Matrix Common Y Bit := fun s y => c s.1 y s.2
  have factored : left * right = A := by
    ext x y
    rw [Matrix.mul_apply, rep, Fintype.sum_sigma]
    simp only [left, right, Finset.mul_sum, mul_assoc]
  rw [← factored]
  have bound := (Matrix.rank_mul_le_left left right).trans (Matrix.rank_le_card_width left)
  simpa only [Common, Fintype.card_sigma, block_tuple_count] using bound

#print axioms shared_expansion
#print axioms type_block_response_rank
#print axioms product_of_block_trees
#print axioms weighted_squarefree_identity_minor
#print axioms equality_requires
#print axioms weighted_identity_minor
#print axioms cheap_diagonals

end AffineCutRank
