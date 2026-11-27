import Std

namespace OneFaultSyndrome

abbrev Word (q : Nat) := Fin q → Bool

def rightPair {q : Nat} (P Q : Fin q → Fin q) (x : Word q) : Word q :=
  fun i => xor (x (P i)) (x (Q i))

def source {q : Nat} (P Q : Fin q → Fin q) (x : Word q) (b : Bool) : Prop :=
  ∀ i, xor (x i) (rightPair P Q x i) = b

/-- All rows except the root have right side zero. The equalities here are
the Boolean form of the corresponding two-variable homogeneous XOR rows. -/
def lift {n : Nat} (P Q : Fin (n+1) → Fin (n+1)) (x v u t : Word (n+1))
    (b : Bool) : Prop :=
  t 0 = b ∧ (∀ i : Fin n, t i.castSucc = t i.succ) ∧
  (∀ i, v i = x i) ∧ (∀ i, u i = rightPair P Q x i) ∧
  (∀ i, xor (xor (u i) (v i)) (t i) = false)

private theorem xor_row (u v t : Bool) :
    xor (xor u v) t = false ↔ xor v u = t := by
  cases u <;> cases v <;> cases t <;> decide

private theorem chain_constant {n : Nat} (t : Word (n+1)) (b : Bool)
    (root : t 0 = b) (chain : ∀ i : Fin n, t i.castSucc = t i.succ) :
    t = fun _ => b := by
  funext i
  induction i using Fin.induction with
  | zero => exact root
  | succ j ih => exact (chain j).symm.trans ih

/-- Exact fibers for both the one-fault syndrome and the homogeneous
system. P,Q need not be bijective for this algebraic statement. -/
theorem lift_iff {n : Nat} (P Q : Fin (n+1) → Fin (n+1))
    (x v u t : Word (n+1)) (b : Bool) :
    lift P Q x v u t b ↔
      source P Q x b ∧ v = x ∧ u = rightPair P Q x ∧ t = fun _ => b := by
  constructor
  · rintro ⟨root, chain, hv, hu, rows⟩
    have ht := chain_constant t b root chain
    refine ⟨fun i => ?_, funext hv, funext hu, ht⟩
    have row := (xor_row _ _ _).mp (rows i)
    simpa [hv i, hu i, ht] using row
  · rintro ⟨h, rfl, rfl, rfl⟩
    exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun i => (xor_row _ _ _).mpr (h i)⟩

def weight {q : Nat} (x : Word q) : Nat := (List.finRange q).countP x

private theorem complementary_count (xs : List α) (x : α → Bool) :
    xs.countP x + xs.countP (fun i => !(x i)) = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : x a <;> simp [h] <;> omega

private theorem odd_complement (a b : Bool) (h : xor a b = true) : b = !a := by
  revert h
  cases a <;> cases b <;> decide

/-- The selected pair contributes one and the chain contributes one at
each index. This counts physical ones in all four banks. -/
theorem one_fault_weight {n : Nat} (P Q : Fin (n+1) → Fin (n+1))
    (x v u t : Word (n+1)) (h : lift P Q x v u t true) :
    weight x + weight v + weight u + weight t = weight x + 2*(n+1) := by
  obtain ⟨original, hv, hu', ht⟩ := (lift_iff ..).mp h
  rw [hv, hu', ht]
  have hu : rightPair P Q x = fun i => !(x i) :=
    funext fun i => odd_complement _ _ (original i)
  have pair := complementary_count (List.finRange (n+1)) x
  simp only [List.length_finRange] at pair
  simp [weight, hu]
  omega

/-- Subdivide the root equation y=b into a new root z=b and y+z=0.
Every old solution has exactly one new coordinate. -/
theorem root_subdivision {A : Type} (rest : A → Prop) (y : A → Bool)
    (a : A) (z b : Bool) :
    (rest a ∧ z = b ∧ xor (y a) z = false) ↔ (rest a ∧ y a = b ∧ z = b) := by
  cases h : y a <;> cases z <;> cases b <;> simp

/-- Every weight in the original affine coset shifts by exactly one.
In particular so does its minimum whenever the coset is nonempty. -/
theorem successor_weight_spectrum {A : Type} (rest : A → Prop) (y : A → Bool)
    (w : A → Nat) (k : Nat) :
    (∃ a z, (rest a ∧ z = true ∧ xor (y a) z = false) ∧ w a + z.toNat = k+1) ↔
    ∃ a, (rest a ∧ y a = true) ∧ w a = k := by
  constructor
  · rintro ⟨a, z, h, hw⟩
    obtain ⟨ok, root, rfl⟩ := (root_subdivision ..).mp h
    exact ⟨a, ⟨ok, root⟩, by simpa using hw⟩
  · rintro ⟨a, ⟨ok, root⟩, hw⟩
    exact ⟨a, true, (root_subdivision ..).mpr ⟨ok, root, rfl⟩, by simp [hw]⟩

/-- The extra homogeneous row fixes switch b to the complement of a
distinguished bit h once the terminal root-chain value is one. -/
theorem switch_row (b h : Bool) : xor (xor b h) true = false ↔ b = !h := by
  cases b <;> cases h <;> decide

def switchedWeight {A : Type} (q : Nat) (w : A → Nat) (bit : A → Bool) (a : A) :=
  2*q + w a + (!(bit a)).toNat

/-- The supplied near word and every optimum are at adjacent weights in
the no case; an original exact cover attains the lower radius exactly. -/
theorem one_unit_gap {A : Type} (q k : Nat) (valid : A → Prop) (w : A → Nat)
    (bit : A → Bool)
    (gap : ∀ a, valid a → w a = k ∨ k+2 ≤ w a)
    (off : ∀ a, valid a → w a = k → bit a = false)
    (known : A) (hv : valid known) (hw : w known = k+2) (hon : bit known = true) :
    let R := 2*q+k+1
    switchedWeight q w bit known = R+1 ∧
    (∀ a, valid a → R ≤ switchedWeight q w bit a) ∧
    (∀ a, valid a → (switchedWeight q w bit a = R ↔ w a = k)) ∧
    ((¬ ∃ a, valid a ∧ w a = k) →
      (∀ a, valid a → R+1 ≤ switchedWeight q w bit a) ∧
      ∃ a, valid a ∧ switchedWeight q w bit a = R+1) := by
  dsimp only
  have supplied : switchedWeight q w bit known = 2*q+k+1+1 := by
    simp [switchedWeight, hw, hon]
    omega
  have each (a : A) (va : valid a) :
      (w a = k ∧ switchedWeight q w bit a = 2*q+k+1) ∨
      (k+2 ≤ w a ∧ 2*q+k+1+1 ≤ switchedWeight q w bit a) := by
    rcases gap a va with eq | large
    · exact Or.inl ⟨eq, by simp [switchedWeight, eq, off a va eq]⟩
    · exact Or.inr ⟨large, by unfold switchedWeight; omega⟩
  refine ⟨supplied, fun a va => ?_, fun a va => ?_, fun no => ⟨?_, ⟨known,hv,supplied⟩⟩⟩
  · rcases each a va with ⟨_,h⟩ | ⟨_,h⟩ <;> omega
  · rcases each a va with ⟨e,h⟩ | ⟨e,h⟩ <;> omega
  · intro a va
    rcases each a va with ⟨e,_⟩ | ⟨_,h⟩
    · exact False.elim (no ⟨a,va,e⟩)
    · exact h

namespace Graph

def parity (xs : List α) (f : α → Bool) : Bool := xs.foldr (fun i b => xor (f i) b) false

private theorem parity_zero (xs : List α) (f : α → Bool) (h : ∀ i ∈ xs, f i = false) :
    parity xs f = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change xor (f x) (parity xs f) = false
    simp [h x (by simp), ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

private theorem parity_add (xs : List α) (f g : α → Bool) :
    parity xs (fun i => xor (f i) (g i)) = xor (parity xs f) (parity xs g) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change xor (xor (f i) (g i)) (parity xs _) =
      xor (xor (f i) (parity xs f)) (xor (g i) (parity xs g))
    rw [ih]
    cases f i <;> cases g i <;> cases parity xs f <;> cases parity xs g <;> decide

private theorem mult_parity (b : Bool) (xs : List α) (f : α → Bool) :
    (b && parity xs f) = parity xs (fun i => b && f i) := by
  cases b with
  | false => simpa using (parity_zero xs (fun _ => false) (by simp)).symm
  | true => simp

private theorem symmetric_sum (vs : List α) (e : α → α → Bool)
    (diag : ∀ i, e i i = false) (symm : ∀ i j, e i j = e j i) :
    parity vs (fun i => parity vs (e i)) = false := by
  induction vs with
  | nil => rfl
  | cons a vs ih =>
    change xor (xor (e a a) (parity vs (e a)))
      (parity vs (fun i => xor (e i a) (parity vs (e i)))) = false
    rw [parity_add, ih, diag, show (fun i => e i a) = e a from funext (fun i => symm i a)]
    cases parity vs (e a) <;> decide

def adjacent (vs : List α) (edge : α → α → Bool) (x : α → Bool) (i : α) :=
  parity vs (fun j => edge i j && x j)

/-- Alternating adjacency form in characteristic two. -/
theorem self_dot_zero (vs : List α) (edge : α → α → Bool) (x : α → Bool)
    (diag : ∀ i, edge i i = false) (symm : ∀ i j, edge i j = edge j i) :
    parity vs (fun i => x i && adjacent vs edge x i) = false := by
  let e := fun i j => x i && (edge i j && x j)
  have eq (i) : (x i && adjacent vs edge x i) = parity vs (e i) :=
    mult_parity _ _ _
  rw [show (fun i => x i && adjacent vs edge x i) = _ from funext eq]
  apply symmetric_sum
  · intro i
    simp [e, diag]
  · intro i j
    change (x i && (edge i j && x j)) = (x j && (edge j i && x i))
    rw [symm i j]
    cases x i <;> cases x j <;> simp

/-- If Ax=e_r for a loopless undirected graph then x_r=0. List the
source root once at the beginning of the vertex enumeration. -/
theorem root_off [DecidableEq α] (r : α) (others : List α) (hr : r ∉ others)
    (edge : α → α → Bool) (x : α → Bool)
    (diag : ∀ i, edge i i = false) (symm : ∀ i j, edge i j = edge j i)
    (rhs : ∀ i, adjacent (r :: others) edge x i = decide (i = r)) : x r = false := by
  have dot := self_dot_zero (r :: others) edge x diag symm
  change xor (x r && adjacent _ edge x r)
    (parity others (fun i => x i && adjacent (r :: others) edge x i)) = false at dot
  have off := parity_zero others (fun i => x i && adjacent (r :: others) edge x i)
    (fun i hi => by
      have ne : i ≠ r := by rintro rfl; exact hr hi
      simp [rhs, ne])
  simpa [rhs r, off] using dot

/-- Move the unique syndrome from r to the new leaf of a two-edge tail.
Old root receives the middle bit, and the middle sees the old root and leaf. -/
theorem moved_syndrome_iff [DecidableEq α] (r : α) (old x : α → Bool)
    (mid leaf : Bool) (rootOff : (∀ i, old i = decide (i = r)) → x r = false) :
    ((∀ i, xor (old i) (if i = r then mid else false) = false) ∧
      xor (x r) leaf = false ∧ mid = true) ↔
    ((∀ i, old i = decide (i = r)) ∧ mid = true ∧ leaf = false) := by
  constructor
  · rintro ⟨rows, middle, rfl⟩
    have rhs (i) : old i = decide (i = r) := by
      have h := rows i
      by_cases eq : i = r <;> cases v : old i <;> simp_all
    have hx := rootOff rhs
    exact ⟨rhs, rfl, by simpa [hx] using middle⟩
  · rintro ⟨rhs, rfl, rfl⟩
    refine ⟨fun i => ?_, by simp [rootOff rhs], rfl⟩
    by_cases eq : i = r <;> simp [rhs, eq]

end Graph
end OneFaultSyndrome
