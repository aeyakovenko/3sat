import Std

namespace TwoArmFactors

abbrev Matrix (R C : Type) := R → C → Bool
abbrev RankOne (R C : Type) := (R → Bool) × (C → Bool)

def parity (xs : List α) (f : α → Bool) : Bool :=
  match xs with
  | [] => false
  | x :: rest => f x ^^ parity rest f

def eval (terms : List (RankOne R C)) (i : R) (j : C) : Bool :=
  parity terms (fun p => p.1 i && p.2 j)

def product (ks : List K) (a : K → R → Bool) (b : K → C → Bool) (i : R) (j : C) : Bool :=
  parity ks (fun k => a k i && b k j)

def blocks (tl : Matrix T L) (tr : Matrix T R) (bl : Matrix B L) (br : Matrix B R) :
    Matrix (T ⊕ B) (L ⊕ R)
  | .inl i, .inl j => tl i j
  | .inl i, .inr j => tr i j
  | .inr i, .inl j => bl i j
  | .inr i, .inr j => br i j

/-- G and u choose the two parts of each column of the first factor.
    H and v choose the two parts of each row of the second factor. -/
def stageTerm (g : K → T → Bool) (u : K → B → Bool)
    (h : K → L → Bool) (v : K → R → Bool) (k : K) : RankOne (T ⊕ B) (L ⊕ R) :=
  (Sum.elim (g k) (u k), Sum.elim (h k) (v k))

def pad (p : RankOne B R) : RankOne (T ⊕ B) (L ⊕ R) :=
  (Sum.elim (fun _ => false) p.1, Sum.elim (fun _ => false) p.2)

def combine (ks : List K) (g : K → T → Bool) (u : K → B → Bool)
    (h : K → L → Bool) (v : K → R → Bool) (rest : List (RankOne B R)) :=
  ks.map (stageTerm g u h v) ++ rest.map pad

private theorem parityAppend (xs ys : List α) (f : α → Bool) :
    parity (xs ++ ys) f = (parity xs f ^^ parity ys f) := by
  induction xs with
  | nil => simp [parity]
  | cons x xs ih => simp [parity, ih, Bool.xor_assoc]

private theorem parityMap (xs : List α) (g : α → β) (f : β → Bool) :
    parity (xs.map g) f = parity xs (fun i => f (g i)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [parity, ih]

private theorem parityZero (xs : List α) : parity xs (fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [parity, ih]

/-- The returned list itself witnesses the additive rank budget. -/
theorem rankBudget (ks : List K) (g : K → T → Bool) (u : K → B → Bool)
    (h : K → L → Bool) (v : K → R → Bool) (rest : List (RankOne B R)) :
    (combine ks g u h v rest).length = ks.length + rest.length := by simp [combine]

/-- The corner and both arms are independent of all later factors. On the
    remaining block the first stage and the padded residual add over F₂. -/
theorem fourBlocks (ks : List K) (g : K → T → Bool) (u : K → B → Bool)
    (h : K → L → Bool) (v : K → R → Bool) (rest : List (RankOne B R)) :
    eval (combine ks g u h v rest) =
      blocks (product ks g h) (product ks g v) (product ks u h)
        (fun i j => product ks u v i j ^^ eval rest i j) := by
  funext i j
  cases i <;> cases j <;>
    simp [eval, combine, blocks, product, parityAppend, parityMap, stageTerm, pad, parityZero]

/-- A residual approximation's error indicator is exactly the error on
    the corresponding entry in the final bottom-right block. -/
theorem residualError (ks : List K) (g : K → T → Bool) (u : K → B → Bool)
    (h : K → L → Bool) (v : K → R → Bool) (rest : List (RankOne B R))
    (target : Matrix B R) (i : B) (j : R) :
    (eval (combine ks g u h v rest) (.inr i) (.inr j) != target i j) =
      (eval rest i j != (target i j ^^ product ks u v i j)) := by
  rw [fourBlocks]
  change ((product ks u v i j ^^ eval rest i j) != target i j) = _
  cases product ks u v i j <;> cases eval rest i j <;> cases target i j <;> rfl

/-- A factorization of an already corrected block constructs explicit
    factors for the prescribed bottom-right approximant and the three arms. -/
theorem assembleCorrected (ks : List K) (g : K → T → Bool) (u : K → B → Bool)
    (h : K → L → Bool) (v : K → R → Bool) (rest : List (RankOne B R))
    (approx : Matrix B R) (corrected : ∀ i j, eval rest i j = (approx i j ^^ product ks u v i j)) :
    ∃ terms : List (RankOne (T ⊕ B) (L ⊕ R)),
      terms.length = ks.length + rest.length ∧
      eval terms = blocks (product ks g h) (product ks g v) (product ks u h) approx := by
  refine ⟨combine ks g u h v rest, rankBudget .., ?_⟩
  rw [fourBlocks]
  apply congrArg (blocks (product ks g h) (product ks g v) (product ks u h))
  funext i j
  rw [corrected]
  cases product ks u v i j <;> cases approx i j <;> rfl

end TwoArmFactors
