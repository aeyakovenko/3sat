import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace CrossCharacteristicProductWidth

variable {F : Type*} [Field F]

abbrev Bit := ZMod 2
abbrev Word (d : ℕ) := Fin d → Bit

def sign (b : Bit) : F := if b = 0 then 1 else -1

private theorem bit_cases : ∀ a : Bit, a=0 ∨ a=1 := by decide

private theorem sign_add (a b : Bit) : sign (F := F) (a+b) = sign a * sign b := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases b with rfl|rfl <;>
    simp [sign, show (1:Bit) + 1 = 0 by decide]

private theorem sign_sum {I : Type*} (s : Finset I) (f : I → Bit) :
    sign (F := F) (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert i s hi ih => simp [hi, sign_add, ih]

def walsh (d : ℕ) : Matrix (Word d) (Word d) F :=
  Matrix.of (fun u x => sign (∑ i, u i * x i))

private theorem factor_sum (u v : Bit) :
    (∑ x : Bit, sign (F := F) (u*x) * sign (x*v)) = if u=v then 2 else 0 := by
  have two : (Finset.univ : Finset Bit) = {0,1} := by decide
  rw [two, Finset.sum_insert (by decide), Finset.sum_singleton]
  rcases bit_cases u with rfl|rfl <;> rcases bit_cases v with rfl|rfl <;>
    simp [sign] <;> ring

theorem walsh_square (d : ℕ) :
    (walsh d : Matrix _ _ F) * walsh d = (2^d : F) • 1 := by
  classical
  ext u v
  simp only [Matrix.mul_apply, walsh, Matrix.of_apply, sign_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bit) => sign (F := F) (u i*b) * sign (b*v i))]
  simp only [factor_sum, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases equal : u=v
  · subst v; simp
  · have bad : ∃ i, u i ≠ v i := by
      by_contra! good
      exact equal (funext good)
    obtain ⟨i, hi⟩ := bad
    simp only [equal, ↓reduceIte, mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem walsh_full_rank (d : ℕ) (odd : (2:F) ≠ 0) :
    (walsh d : Matrix _ _ F).rank = 2^d := by
  have left := Matrix.rank_mul_le_left (walsh (F := F) d) (walsh (F := F) d)
  have upper := Matrix.rank_le_card_width (walsh (F := F) d)
  rw [walsh_square] at left
  have scaled : ((2^d : F) • (1 : Matrix (Word d) (Word d) F)).rank = 2^d := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ odd))]
    simp [Word, Bit, ZMod.card]
  rw [scaled] at left
  apply le_antisymm _ left
  simpa [Word, Bit, ZMod.card] using upper

/-- Distinguishing the two values of a binary inner product with a separated
    width-h dot product requires h+1 at least the size of the Walsh matrix. -/
theorem scalar_width {d h : ℕ} (odd : (2:F) ≠ 0) (a b : F) (different : a ≠ b)
    (L : Word d → Fin h → F) (R : Fin h → Word d → F)
    (outputs : ∀ u v, (∑ i, L u i * R i v) =
      if (∑ j, u j * v j) = 0 then a else b) :
    2^d ≤ h+1 := by
  classical
  let c : F := 2/(b-a)
  have hc : c*(b-a)=2 := div_mul_cancel₀ _ (sub_ne_zero.mpr different.symm)
  let L' : Matrix (Word d) (Option (Fin h)) F := Matrix.of fun u i =>
    match i with
    | none => 1
    | some k => -c * L u k
  let R' : Matrix (Option (Fin h)) (Word d) F := Matrix.of fun i v =>
    match i with
    | none => 1+c*a
    | some k => R k v
  have factored : L' * R' = walsh d := by
    ext u v
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [L', R', Matrix.of_apply, one_mul, mul_assoc, ← Finset.mul_sum,
      outputs, walsh, sign]
    split
    · ring
    · linear_combination -hc
  have bound := (Matrix.rank_mul_le_left L' R').trans (Matrix.rank_le_card_width L')
  rw [factored, walsh_full_rank d odd] at bound
  simpa using bound

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) Bit

def rowAt {d} (t : Fin d) (u : Word d) : Square d :=
  Matrix.of fun i j => if i=t then u j else 0

def colAt {d} (s : Fin d) (v : Word d) : Square d :=
  Matrix.of fun i j => if j=s then v i else 0

theorem single_product {d} (t s : Fin d) (u v : Word d) :
    rowAt t u * colAt s v =
    if (∑ i, u i * v i) = 0 then 0 else Matrix.single t s 1 := by
  classical
  rcases bit_cases (∑ i, u i * v i) with dz|do'
  · simp only [dz, ↓reduceIte]
    ext i j
    by_cases ht : i=t <;> by_cases hs : j=s <;>
      simp [Matrix.mul_apply, rowAt, colAt, ht, hs, dz]
  · simp only [do', one_ne_zero, ↓reduceIte]
    ext i j
    by_cases ht : i=t <;> by_cases hs : j=s <;>
      simp_all [Matrix.mul_apply, Matrix.single, rowAt, colAt, eq_comm]

/-- L and R may be arbitrarily nonlinear separate encoders. One output
    coordinate distinguishing the zero product from a matrix unit suffices. -/
theorem encoder_width {d h : ℕ} {I J : Type*} (odd : (2:F) ≠ 0)
    (t s : Fin d) (L : Square d → Matrix I (Fin h) F)
    (R : Square d → Matrix (Fin h) J F) (O : Square d → Matrix I J F)
    (faithful : ∀ A B, L A * R B = O (A*B))
    (different : O 0 ≠ O (Matrix.single t s 1)) :
    2^d ≤ h+1 := by
  classical
  obtain ⟨i,j,dist⟩ : ∃ i j, O 0 i j ≠ O (Matrix.single t s 1) i j := by
    by_contra! same
    exact different (Matrix.ext same)
  apply scalar_width odd _ _ dist (fun u k => L (rowAt t u) i k)
    (fun k v => R (colAt s v) k j)
  intro u v
  have eq := congrFun (congrFun (faithful (rowAt t u) (colAt s v)) i) j
  rw [single_product] at eq
  split at eq <;> simp_all [Matrix.mul_apply]

/-- A truth-table decoder is a weighted sum of the indicators for its
    possible answer strings. -/
private theorem decoder_table {m : ℕ} (f : (Fin m → Bool) → F) (x : Fin m → Bool) :
    f x = ∑ y : Fin m → Bool, f y * ∏ j, (if x j = y j then (1:F) else 0) := by
  classical
  have cell (y : Fin m → Bool) :
      (∏ j, (if x j = y j then (1:F) else 0)) = if y=x then 1 else 0 := by
    by_cases e : y=x
    · subst y; simp
    · have bad : ∃ j, x j ≠ y j := by
        by_contra! good
        exact e (funext good).symm
      obtain ⟨j, hj⟩ := bad
      simp only [e, ↓reduceIte]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
  simp_rw [cell]
  simp

/-- Nonadaptive Boolean measurement results can be decoded arbitrarily. The
    common space of row features has at most (h+1)^m dimensions. -/
theorem boolean_measurements_width {d m h : ℕ} (odd : (2:F) ≠ 0)
    (answers : Fin m → Word d → Word d → Bool)
    (L : Fin m → Word d → Fin h → F) (R : Fin m → Fin h → Word d → F)
    (measured : ∀ j u v, (∑ k, L j u k * R j k v) =
        if answers j u v then (1:F) else 0)
    (decode : (Fin m → Bool) → F)
    (correct : ∀ u v, decode (fun j => answers j u v) = walsh d u v) :
    2^d ≤ (h+1)^m := by
  classical
  let α (j : Fin m) (u : Word d) : Option (Fin h) → F
    | none => 1
    | some k => L j u k
  let β (j : Fin m) (v : Word d) (y : Bool) : Option (Fin h) → F
    | none => if y then 0 else 1
    | some k => if y then R j k v else -R j k v
  have one_test (j : Fin m) (u v : Word d) (y : Bool) :
      (∑ k, α j u k * β j v y k) = if answers j u v = y then 1 else 0 := by
    have eq := measured j u v
    cases y <;> cases hs : answers j u v <;>
      simp [hs] at eq <;> simp [Fintype.sum_option, α, β, eq]
  let rows : Matrix (Word d) (Fin m → Option (Fin h)) F :=
    Matrix.of fun u choice => ∏ j, α j u (choice j)
  let cols : Matrix (Fin m → Option (Fin h)) (Word d) F :=
    Matrix.of fun choice v => ∑ y : Fin m → Bool, decode y * ∏ j, β j v (y j) (choice j)
  have represents : rows * cols = walsh d := by
    ext u v
    rw [← correct, decoder_table decode (fun j => answers j u v)]
    simp only [Matrix.mul_apply, rows, cols, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp_rw [← one_test _ u v _]
    rw [Fintype.prod_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro choice _
    rw [Finset.prod_mul_distrib]
    ring
  have bound := (Matrix.rank_mul_le_left rows cols).trans (Matrix.rank_le_card_width rows)
  rw [represents, walsh_full_rank d odd] at bound
  simpa using bound

end CrossCharacteristicProductWidth
