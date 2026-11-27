import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block

/-! Dimension of the span of raw-word cylinders on an ordered certificate family.
The alphabet may be different at every word. Checked with Lean 4.34.1 and Mathlib. -/

open Finset
open scoped BigOperators

namespace WitnessedInterface

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable {γ : Type} [Fintype γ] [DecidableEq γ]

def basisBit (base u x : γ) : ℚ := if u = base ∨ u = x then 1 else 0

def coeff (base : γ) (f : γ → ℚ) (u : γ) : ℚ :=
  if u = base then f base else f u - f base

private theorem one_cell (base x : γ) (f : γ → ℚ) :
    ∑ u, coeff base f u * basisBit base u x = f x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ base)]
  simp only [coeff, basisBit, true_or]
  have rewriteSum :
      (∑ u ∈ Finset.univ.erase base,
        (if u = base then f base else f u - f base) * (if u = base ∨ u = x then 1 else 0)) =
      ∑ u ∈ Finset.univ.erase base, if u = x then f u - f base else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    have h := (Finset.mem_erase.mp hu).1
    simp [h, mul_ite]
  rw [rewriteSum]
  by_cases h : x = base <;> simp [h]

def localTest (obs : Finset ι) (a : ∀ i, α i) (i : ι) (x : α i) : ℚ :=
  if i ∈ obs then if x = a i then 1 else 0 else 1

def cylinder (obs : Finset ι) (a x : ∀ i, α i) : ℚ :=
  ∏ i, localTest obs a i (x i)

def support (base g : ∀ i, α i) : Finset ι := univ.filter fun i => g i ≠ base i

def weight (base : ∀ i, α i) (s : Finset ι) (a g : ∀ i, α i) : ℚ :=
  ∏ i, coeff (base i) (localTest s a i) (g i)

def feature (base g x : ∀ i, α i) : ℚ := ∏ i, basisBit (base i) (g i) (x i)

private theorem expanded (base : ∀ i, α i) (s : Finset ι) (a x : ∀ i, α i) :
    (∑ g, weight base s a g * feature base g x) = cylinder s a x := by
  simp only [weight, feature, cylinder, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i u => coeff (base i) (localTest s a i) u * basisBit (base i) u (x i))]
  simp only [one_cell]

omit [∀ i, Fintype (α i)] in
private theorem unsupported (base : ∀ i, α i) (s : Finset ι) (a g : ∀ i, α i)
    (h : s.card < (support base g).card) : weight base s a g = 0 := by
  have hn : ¬ support base g ⊆ s := fun hg => (Nat.not_lt.mpr (Finset.card_le_card hg)) h
  obtain ⟨i, hi, hnot⟩ := Finset.not_subset.mp hn
  have hneq := (Finset.mem_filter.mp hi).2
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coeff, localTest, hnot, hneq])

/-- Feature indices recording at most t departures from a chosen base vector. -/
abbrev Small (base : ∀ i, α i) (t : ℕ) := {g : (∀ i, α i) // (support base g).card ≤ t}

theorem small_expansion (base : ∀ i, α i) (s : Finset ι) (a x : ∀ i, α i) (hs : s.card ≤ t) :
    (∑ g : Small base t, weight base s a g * feature base g x) = cylinder s a x := by
  classical
  let test := fun g : (∀ i, α i) => (support base g).card ≤ t
  have vanish : (∑ g : {g // ¬ test g}, weight base s a g * feature base g x) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    have hp := unsupported base s a g (Nat.lt_of_le_of_lt hs (Nat.lt_of_not_ge g.property))
    simp [hp]
  have hp := Fintype.sum_subtype_add_sum_subtype test (fun g => weight base s a g * feature base g x)
  rw [← expanded base s a x]
  simpa only [vanish, add_zero] using hp
end WitnessedInterface
namespace WitnessedInterface

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

/-- Each sample has a t-cell certificate excluding all later samples. -/
theorem ordered_cylinders (base : ∀ i, α i) (db : Fin n → ∀ i, α i) (tests : Fin n → Finset ι)
    (budget : ∀ h, (tests h).card ≤ t)
    (excludes : ∀ h j, h < j → ∃ i ∈ tests h, db j i ≠ db h i) :
    n ≤ Fintype.card (Small base t) := by
  classical
  let A : Matrix (Fin n) (Small base t) ℚ :=
    Matrix.of fun h g => weight base (tests h) (db h) g
  let B : Matrix (Small base t) (Fin n) ℚ :=
    Matrix.of fun g j => feature base g (db j)
  have entry (h j : Fin n) : (A * B) h j = cylinder (tests h) (db h) (db j) := by
    exact small_expansion base (tests h) (db h) (db j) (budget h)
  have diag (h : Fin n) : (A * B) h h = 1 := by
    rw [entry]
    simp [cylinder, localTest]
  have tri : (A * B).IsLowerTriangular := by
    intro h j lt
    obtain ⟨i, hi, hneq⟩ := excludes h j lt
    rw [entry]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [localTest, hi, hneq])
  have hd : (A * B).det = 1 := by rw [Matrix.det_of_isLowerTriangular _ tri]; simp [diag]
  have hr := Matrix.rank_of_det_ne_zero (by rw [hd]; exact one_ne_zero)
  have hb := (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)
  simpa [hr] using hb

#print axioms ordered_cylinders
end WitnessedInterface
namespace WitnessedInterface

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {α : ι → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]

abbrev Menu (t : ℕ) := {s : Finset ι // s.card ≤ t}
abbrev Alternatives (base : ∀ i, α i) (s : Finset ι) :=
  ∀ i : s, {v : α i // v ≠ base i}

def fill (base : ∀ i, α i) (s : Finset ι) (v : Alternatives base s) (i : ι) : α i :=
  if h : i ∈ s then (v ⟨i,h⟩).val else base i

omit [∀ i, Fintype (α i)] in
theorem support_fill (base : ∀ i, α i) (s : Finset ι) (v : Alternatives base s) :
    support base (fill base s v) = s := by
  ext i
  by_cases hi : i ∈ s
  · simp [support, fill, hi, (v ⟨i,hi⟩).property]
  · simp [support, fill, hi]

def fillSmall (base : ∀ i, α i) (v : (s : Menu (ι:=ι) t) × Alternatives base s.val) : Small base t :=
  ⟨fill base v.1.val v.2, by simpa [support_fill] using v.1.property⟩

omit [∀ i, Fintype (α i)] in
private theorem fill_bijective (base : ∀ i, α i) (t : ℕ) :
    Function.Bijective (fillSmall (t:=t) base) := by
  constructor
  · intro ⟨s,vs⟩ ⟨r,vr⟩ he
    have he' := congrArg Subtype.val he
    have sr := congrArg (support base) he'
    have eq : s = r := Subtype.ext (by simpa [fillSmall, support_fill] using sr)
    subst r
    have same : vs = vr := by
      funext i
      apply Subtype.ext
      have valEq := congrFun he' i.val
      simpa [fillSmall,fill,i.property] using valEq
    subst vr
    rfl
  · intro g
    let s : Menu (ι:=ι) t := ⟨support base g, g.property⟩
    let v : Alternatives base s.val := fun i => ⟨g.val i, (Finset.mem_filter.mp i.property).2⟩
    refine ⟨⟨s,v⟩, Subtype.ext (funext fun i => ?_)⟩
    by_cases hi : i ∈ s.val
    · simp [fillSmall,fill,hi,v]
    · have he : g.val i = base i := by simpa [s,support] using hi
      simp [fillSmall,fill,hi,he]

theorem feature_count (base : ∀ i, α i) (t : ℕ) :
    Fintype.card (Small base t) =
      ∑ s : Menu (ι:=ι) t, ∏ i : s.val, Fintype.card {v : α i // v ≠ base i} := by
  classical
  have h := Fintype.card_congr (Equiv.ofBijective (fillSmall (t:=t) base) (fill_bijective base t))
  rw [← h, Fintype.card_sigma]
  exact Finset.sum_congr rfl fun s _ => Fintype.card_pi (α := fun i : s.val => {v : α i // v ≠ base i})

omit [DecidableEq ι] [∀ i, Fintype (α i)] in
/-- Within the low-support class about the top database, agreement on the exceptional
words certifies coordinatewise containment. -/
theorem top_class_certificate [∀ i, PartialOrder (α i)] [∀ i, OrderTop (α i)]
    (a : Small (fun i => (⊤ : α i)) t) (b : ∀ i, α i)
    (agrees : ∀ i ∈ support (fun i => (⊤ : α i)) a, b i = a.val i) :
    b ≤ a.val := by
  intro i
  by_cases hi : a.val i = ⊤
  · rw [hi]
    exact le_top
  · exact (agrees i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)).le

#print axioms feature_count
#print axioms top_class_certificate
end WitnessedInterface
