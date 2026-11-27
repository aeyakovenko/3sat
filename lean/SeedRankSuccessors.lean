import Std

/-! Four physical variables, numbered from least to most significant bit.
Each row consists of clauses on the triple obtained by omitting its row
index. A clause sign is the unique forbidden 3-bit assignment on its row. -/

namespace SeedRankSuccessors

def pack3 (a b c : Bool) : BitVec 3 :=
  BitVec.ofNat 3 (a.toNat + 2*b.toNat + 4*c.toNat)

def pack4 (a b c d : Bool) : BitVec 4 :=
  BitVec.ofNat 4 (a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat)

/-- Tuple coordinates follow increasing physical variable number. -/
def row (i : Fin 4) (x : BitVec 4) : BitVec 3 :=
  let bit := x.getLsbD
  match i.val with
  | 0 => pack3 (bit 1) (bit 2) (bit 3)
  | 1 => pack3 (bit 0) (bit 2) (bit 3)
  | 2 => pack3 (bit 0) (bit 1) (bit 3)
  | _ => pack3 (bit 0) (bit 1) (bit 2)

def parity (x : BitVec 3) : Bool := x.getLsbD 0 ^^ x.getLsbD 1 ^^ x.getLsbD 2

def syndrome (x : BitVec 4) : BitVec 4 :=
  pack4 (parity (row 0 x)) (parity (row 1 x)) (parity (row 2 x)) (parity (row 3 x))

/-- Linearity and a two-sided inverse (the matrix itself) give binary rank four. -/
theorem syndrome_linear : ∀ x y, syndrome (x ^^^ y) = syndrome x ^^^ syndrome y := by decide
theorem syndrome_inverse : ∀ x, syndrome (syndrome x) = x := by decide

abbrev Clause := Fin 4 × BitVec 3

def accepts (cs : List Clause) (x : BitVec 4) : Bool :=
  cs.all (fun c => row c.1 x != c.2)

def signs : List (BitVec 3) := (List.finRange 8).map (fun i => BitVec.ofNat 3 i.val)

/-- Each of the four proper clauses excludes one sign of the wrong parity. -/
def paritySigns (rhs : Bool) := signs.filter (fun s => parity s != rhs)

def parityCNF (target : BitVec 4) : List Clause :=
  (List.finRange 4).flatMap (fun i =>
    (paritySigns (parity (row i target))).map (fun s => (i, s)))

theorem parity_sign_count : ∀ rhs, (paritySigns rhs).length = 4 ∧ (paritySigns rhs).Nodup := by decide

theorem parity_unique : ∀ target x, accepts (parityCNF target) x = true ↔ x = target := by decide

/-- A single row allows every prescribed pair of distinct coordinates,
including both settings of each individual literal. -/
theorem pair_extends_on_parity_row : ∀ (rhs : Bool) (i j : Fin 3), i ≠ j →
    ∀ a b : Bool, ∃ x : BitVec 3, x ∉ paritySigns rhs ∧
      x.getLsbD i.val = a ∧ x.getLsbD j.val = b := by decide

/-- An eight-clause alternative with no complete parity bucket on any triple. -/
def sparseSigns (i : Fin 4) : List (BitVec 3) :=
  match i.val with
  | 0 => [1, 2, 3]
  | 1 => [4, 6]
  | 2 => [5, 7]
  | _ => [1]

def shiftedSigns (i : Fin 4) (target : BitVec 4) :=
  (sparseSigns i).map (fun s => s ^^^ row i target)

def sparseCNF (target : BitVec 4) : List Clause :=
  (List.finRange 4).flatMap (fun i => (shiftedSigns i target).map (fun s => (i,s)))

theorem sparse_unique : ∀ target x, accepts (sparseCNF target) x = true ↔ x = target := by decide

theorem sparse_size : ∀ target, (sparseCNF target).length = 8 ∧ (sparseCNF target).Nodup := by decide

/-- For every nonzero coefficient vector, both parities occur among the allowed
local patterns. In particular a sign shift cannot create a locally forced literal. -/
theorem sparse_no_local_affine_equation :
    ∀ (i : Fin 4) (target : BitVec 4) (coeff : BitVec 3), coeff ≠ 0 →
    ∀ desired : Bool, ∃ x : BitVec 3, x ∉ shiftedSigns i target ∧
      parity (x &&& coeff) = desired := by decide

def assignments : List (BitVec 4) :=
  (List.finRange 16).map (fun i => BitVec.ofNat 4 i.val)

private theorem union_bound (xs : List α) (p q : α → Bool) :
    (xs.filter (fun x => p x || q x)).length ≤ (xs.filter p).length + (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp [List.filter_cons, hp, hq] <;> omega

/-- Each proper three-variable clause on these four names excludes exactly two
assignments, so eight clauses is optimal even when the signs and rows are arbitrary. -/
theorem refuted_count (cs : List Clause) :
    (assignments.filter (fun x => !(accepts cs x))).length ≤ 2 * cs.length := by
  induction cs with
  | nil => simp [accepts]
  | cons c cs ih =>
    have flags : (fun x => !(accepts (c :: cs) x)) =
        (fun x => (row c.1 x == c.2) || !(accepts cs x)) := by
      funext x
      simp [accepts, bne, BEq.beq]
    have two : ∀ i s, (assignments.filter (fun x => row i x == s)).length = 2 := by decide
    rw [flags]
    have ub := union_bound assignments (fun x => row c.1 x == c.2) (fun x => !(accepts cs x))
    rw [two] at ub
    simp only [List.length_cons]
    omega

theorem minimum_clauses (cs : List Clause) (target : BitVec 4)
    (unique : ∀ x, accepts cs x = true ↔ x = target) : 8 ≤ cs.length := by
  have flags : (fun x => !(accepts cs x)) = (fun x => x != target) := by
    funext x
    by_cases eq : x = target
    · subst x
      simp [(unique target).2 rfl]
    · have h : accepts cs x ≠ true := fun e => eq ((unique x).1 e)
      simp [Bool.eq_false_iff.mpr h, bne, eq]
  have fifteen : ∀ t : BitVec 4, (assignments.filter (fun x => x != t)).length = 15 := by decide
  have bound := refuted_count cs
  rw [flags, fifteen] at bound
  omega

/-- A block placed in the most significant position leaves all lower-order
coordinates free in this estimate. Enumeration starts from the zero assignment. -/
theorem high_seed_rank (target : BitVec 4) (high : target.getLsbD 3 = true)
    (suffixBits suffix : Nat) :
    8 * 2^suffixBits ≤ target.toNat * 2^suffixBits + suffix := by
  have h : ∀ x : BitVec 4, x.getLsbD 3 = true → 8 ≤ x.toNat := by decide
  exact Nat.le_trans (Nat.mul_le_mul_right _ (h target high)) (Nat.le_add_right _ _)

end SeedRankSuccessors
