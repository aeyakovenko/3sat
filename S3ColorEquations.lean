import Std

/-! The permutations of three colors are the affine maps
`i ↦ a + i` and `i ↦ a - i` on the residues modulo three.
Use these coordinates to encode a graph edge by one conjugacy equation. -/

namespace S3ColorEquations

private instance decideExistsFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ x, p x) :=
  decidable_of_iff (¬ ∀ x, ¬ p x) (by classical simp)

abbrev Color := Fin 3
abbrev Perm := Fin 6

def pack (a : Color) (reflected : Bool) : Perm :=
  ⟨a.val + (if reflected then 3 else 0), by
    have ha := a.isLt
    split <;> omega⟩

def shift (x : Perm) : Color := ⟨x.val % 3, Nat.mod_lt _ (by decide)⟩

def reflected (x : Perm) : Bool := decide (3 ≤ x.val)

def sign (b : Bool) (i : Color) : Color := if b then 0 - i else i

def act (x : Perm) (i : Color) : Color := shift x + sign (reflected x) i

def prod (x y : Perm) : Perm :=
  pack (act x (shift y)) (Bool.xor (reflected x) (reflected y))

def inv (x : Perm) : Perm := pack (sign (reflected x) (0 - shift x)) (reflected x)

def one : Perm := pack 0 false

/-- The cycle taking 0 to 1, 1 to 2, and 2 to 0. -/
def cycle : Perm := pack 1 false

/-- Reflection about 0 interchanges 1 and 2. -/
def swap : Perm := pack 0 true

theorem coefficient_bits : cycle.val = 1 ∧ swap.val = 3 ∧
    (cycle.val ^^^ swap.val) = 2 := by decide

theorem act_prod : ∀ x y i, act (prod x y) i = act x (act y i) := by decide

theorem act_inv : ∀ x i, act (inv x) (act x i) = i ∧ act x (act (inv x) i) = i := by
  decide

theorem act_one : ∀ i, act one i = i := by decide

theorem act_faithful : ∀ x y, (∀ i, act x i = act y i) → x = y := by decide

/-- Every injection of the three colors occurs among these six permutations. -/
theorem all_permutations (f : Color → Color)
    (h : ∀ i j, f i = f j → i = j) : ∃ x, ∀ i, act x i = f i := by
  have complete : ∀ a b c : Color, a ≠ b → b ≠ c → a ≠ c →
      ∃ x, act x 0 = a ∧ act x 1 = b ∧ act x 2 = c := by decide
  obtain ⟨x, h0, h1, h2⟩ := complete (f 0) (f 1) (f 2)
    (fun eq => (by decide : (0 : Color) ≠ 1) (h 0 1 eq))
    (fun eq => (by decide : (1 : Color) ≠ 2) (h 1 2 eq))
    (fun eq => (by decide : (0 : Color) ≠ 2) (h 0 2 eq))
  refine ⟨x, fun i => ?_⟩
  have cases3 : ∀ j : Color, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases cases3 i with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- The coefficient is the only parameter changed in the edge test. -/
def edgeWith (g x y k : Perm) : Prop := prod x (inv y) = prod (prod k g) (inv k)

instance (g x y k : Perm) : Decidable (edgeWith g x y k) :=
  inferInstanceAs (Decidable (_ = _))

abbrev edge := edgeWith cycle

theorem edge_iff : ∀ x y, (∃ k, edge x y k) ↔
    reflected x = reflected y ∧ shift x ≠ shift y := by decide

theorem swap_edge_iff : ∀ x y, (∃ k, edgeWith swap x y k) ↔
    reflected x ≠ reflected y := by decide

/-- With orientable auxiliary pairs k,p,q the edge can use three ternary words. -/
theorem ternary_edge (g x y k : Perm) : edgeWith g x y k ↔ ∃ p q,
    prod (prod x (inv y)) (inv p) = one ∧
    prod (prod q (inv g)) (inv k) = one ∧
    prod (prod p k) (inv q) = one := by
  have first : ∀ a b d, prod (prod a (inv b)) (inv d) = one ↔ d = prod a (inv b) := by decide
  have second : ∀ a b d, prod (prod d (inv b)) (inv a) = one ↔ d = prod a b := by decide
  have third : ∀ a b d, prod (prod a b) (inv d) = one ↔ prod a b = d := by decide
  have cancel : ∀ g x y k, edgeWith g x y k ↔ prod (prod x (inv y)) k = prod k g := by
    decide
  constructor
  · intro h
    exact ⟨_, _, (first _ _ _).mpr rfl, (second _ _ _).mpr rfl,
      (third _ _ _).mpr ((cancel _ _ _ _).mp h)⟩
  · rintro ⟨p, q, h₁, h₂, h₃⟩
    have eq := (third _ _ _).mp h₃
    rw [(first _ _ _).mp h₁, (second _ _ _).mp h₂] at eq
    exact (cancel _ _ _ _).mpr eq

universe u v

def ThreeColorable {V : Type u} {E : Type v} (src dst : E → V) : Prop :=
  ∃ color : V → Color, ∀ e, color (src e) ≠ color (dst e)

def Bipartite {V : Type u} {E : Type v} (src dst : E → V) : Prop :=
  ∃ side : V → Bool, ∀ e, side (src e) ≠ side (dst e)

def SolvableWith {V : Type u} {E : Type v} (g : Perm) (src dst : E → V) : Prop :=
  ∃ (label : V → Perm) (conjugator : E → Perm),
    ∀ e, edgeWith g (label (src e)) (label (dst e)) (conjugator e)

/-- The edge index may describe a finite multigraph, including loops.
The shift coordinate extracts the color uniformly in every component. -/
theorem solvable_iff_threeColorable {V : Type u} {E : Type v} (src dst : E → V) :
    SolvableWith cycle src dst ↔ ThreeColorable src dst := by
  constructor
  · rintro ⟨label, conjugator, legal⟩
    exact ⟨fun v => shift (label v), fun e =>
      ((edge_iff _ _).mp ⟨conjugator e, legal e⟩).2⟩
  · rintro ⟨color, proper⟩
    have unpack : ∀ a : Color, reflected (pack a false) = false ∧
        shift (pack a false) = a := by decide
    let label := fun v => pack (color v) false
    have witnesses (e : E) : ∃ k, edge (label (src e)) (label (dst e)) k := by
      apply (edge_iff _ _).mpr
      exact ⟨(unpack _).1.trans (unpack _).1.symm,
        by simpa [label, (unpack _).2] using proper e⟩
    exact ⟨label, fun e => Classical.choose (witnesses e),
      fun e => Classical.choose_spec (witnesses e)⟩

theorem solvable_iff_bipartite {V : Type u} {E : Type v} (src dst : E → V) :
    SolvableWith swap src dst ↔ Bipartite src dst := by
  constructor
  · rintro ⟨label, k, legal⟩
    exact ⟨fun v => reflected (label v),
      fun e => (swap_edge_iff _ _).mp ⟨k e, legal e⟩⟩
  · rintro ⟨side, opposite⟩
    have unpack : ∀ b, reflected (pack 0 b) = b := by decide
    let label := fun v => pack 0 (side v)
    have witnesses (e : E) : ∃ k, edgeWith swap (label (src e)) (label (dst e)) k := by
      apply (swap_edge_iff _ _).mpr
      simpa [label, unpack] using opposite e
    exact ⟨label, fun e => Classical.choose (witnesses e),
      fun e => Classical.choose_spec (witnesses e)⟩

theorem equality_word : ∀ x y, prod x (inv y) = one ↔ x = y := by decide

/-- A nonempty ring contains the successive equality words and the closing word. -/
def Ring {n : Nat} (a : Fin (n + 1) → Perm) : Prop :=
  (∀ i : Fin n, prod (a i.castSucc) (inv (a i.succ)) = one) ∧
  prod (a (Fin.last n)) (inv (a 0)) = one

theorem ring_iff {n : Nat} (a : Fin (n + 1) → Perm) :
    Ring a ↔ ∀ i, a i = a 0 := by
  constructor
  · intro accepted
    exact Fin.induction rfl (fun i ih => ((equality_word _ _).mp (accepted.1 i)).symm.trans ih)
  · intro constant
    exact ⟨fun i => (equality_word _ _).mpr ((constant _).trans (constant _).symm),
      (equality_word _ _).mpr (constant _)⟩

/-- The endpoints of each edge specify the two incidence copies to use.
A vertex with no incidence can be omitted or supplied with a dummy copy.
One can take a distinct copy for every incidence when enforcing multiplicities. -/
def SplitSolvable {V : Type u} {E : Type v} (g : Perm) (src dst : E → V) (extra : V → Nat)
    (leftCopy : (e : E) → Fin (extra (src e) + 1))
    (rightCopy : (e : E) → Fin (extra (dst e) + 1)) : Prop :=
  ∃ (label : (v : V) → Fin (extra v + 1) → Perm) (conjugator : E → Perm),
    (∀ v, Ring (label v)) ∧
    ∀ e, edgeWith g (label (src e) (leftCopy e)) (label (dst e) (rightCopy e)) (conjugator e)

theorem split_iff_unsplit {V : Type u} {E : Type v} (g : Perm)
    (src dst : E → V) (extra : V → Nat)
    (leftCopy : (e : E) → Fin (extra (src e) + 1))
    (rightCopy : (e : E) → Fin (extra (dst e) + 1)) :
    SplitSolvable g src dst extra leftCopy rightCopy ↔ SolvableWith g src dst := by
  constructor
  · rintro ⟨label, k, rings, edges⟩
    refine ⟨fun v => label v 0, k, fun e => ?_⟩
    have accepted := edges e
    rwa [(ring_iff _).mp (rings _) (leftCopy e), (ring_iff _).mp (rings _) (rightCopy e)]
      at accepted
  · rintro ⟨label, k, edges⟩
    exact ⟨fun v _ => label v, k, fun v => (ring_iff _).mpr (fun _ => rfl), edges⟩

section

variable {V : Type u} {E : Type v} (src dst : E → V) (extra : V → Nat)
    (leftCopy : (e : E) → Fin (extra (src e) + 1))
    (rightCopy : (e : E) → Fin (extra (dst e) + 1))

theorem split_iff_threeColorable :
    SplitSolvable cycle src dst extra leftCopy rightCopy ↔ ThreeColorable src dst :=
  (split_iff_unsplit cycle src dst extra leftCopy rightCopy).trans (solvable_iff_threeColorable src dst)

theorem split_iff_bipartite :
    SplitSolvable swap src dst extra leftCopy rightCopy ↔ Bipartite src dst :=
  (split_iff_unsplit swap src dst extra leftCopy rightCopy).trans (solvable_iff_bipartite src dst)

end

/-- The sign equations multiply across rows of a component. -/
theorem parity_rules : (∀ x y, reflected (prod x y) = Bool.xor (reflected x) (reflected y)) ∧
    (∀ x, reflected (inv x) = reflected x) := by decide

/-- One label occurring once in a word can realize any target product. -/
theorem repair_word_slot : ∀ (backwards : Bool) (a b target : Perm), ∃ x : Perm,
    prod (prod a (if backwards then inv x else x)) b = target := by decide

/-- The six-bit table for x a⁻¹ = k g k⁻¹ with k existentially quantified. -/
def translateMask (g a : Perm) : Nat :=
  (List.finRange 6).foldl (fun m x =>
    if ∃ k, edgeWith g x a k then m + 2 ^ x.val else m) 0

theorem translateMask_spec : ∀ g a x,
    (translateMask g a).testBit x.val = true ↔ ∃ k, edgeWith g x a k := by decide

/-- Empty, full, and right translates of the three conjugacy classes. -/
def exampleMasks : List Nat := [0, 63] ++ [one, cycle, swap].flatMap
  (fun g => (List.finRange 6).map (translateMask g))

def oneParity (m : Nat) : Prop := ∀ x y : Perm,
  m.testBit x.val = true → m.testBit y.val = true → reflected x = reflected y

private instance decideParity (m : Nat) : Decidable (oneParity m) :=
  by unfold oneParity; infer_instance

/-- Among all 64 tables, the examples are exactly the full set and the
subsets of a parity coset. The two cosets have only the empty subset in common. -/
theorem unary_table_exhaustion :
    (∀ m : Fin 64, m.val ∈ exampleMasks ↔ m.val = 63 ∨ oneParity m.val) ∧
    exampleMasks.eraseDups.length = 16 := by decide

end S3ColorEquations
