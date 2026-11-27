import Std

namespace SparseProofSupports

def weight (b : Bool) : Nat := if b then 1 else 0

def countOn {ι : Type} (p : ι → Bool) : List ι → Nat
  | [] => 0
  | i :: is => weight (p i) + countOn p is

/-- Two multipliers with a common expanded support can differ only where
    one of their local axiom terms adds a coordinate. -/
theorem expansion_distance {ι : Type} (left right addedLeft addedRight : ι → Bool)
    (same : ∀ i, (left i || addedLeft i) = (right i || addedRight i))
    (coords : List ι) :
    countOn (fun i => left i != right i) coords ≤
      countOn addedLeft coords + countOn addedRight coords := by
  induction coords with
  | nil => simp [countOn]
  | cons i is ih =>
    have h := same i
    have one : weight (left i != right i) ≤ weight (addedLeft i) + weight (addedRight i) := by
      cases hl : left i <;> cases hr : right i <;>
        cases ha : addedLeft i <;> cases hb : addedRight i <;>
        simp_all [weight]
    simp only [countOn]
    omega

theorem width_three_distance {ι : Type} (left right a b : ι → Bool) (coords : List ι)
    (shared : ∀ i, (left i || a i) = (right i || b i))
    (wa : countOn a coords ≤ 3) (wb : countOn b coords ≤ 3) :
    countOn (fun i => left i != right i) coords ≤ 6 := by
  have bound := expansion_distance left right a b shared coords
  omega

/-- Rows lie in the root's component when a path of shared nonzero
    monomial coefficients joins them to the root. -/
inductive Connected {R M K : Type} (entry : R → M → K) (zero : K) (root : R) : R → Prop
  | root_mem : Connected entry zero root root
  | step {u v : R} {m : M} : Connected entry zero root u →
      entry u m ≠ zero → entry v m ≠ zero → Connected entry zero root v

noncomputable def kept {R M K : Type} (entry : R → M → K) (zero : K) (root r : R) (m : M) : K := by
  classical
  exact if Connected entry zero root r then entry r m else zero

def rowSum {R K : Type} (zero : K) (plus : K → K → K) (f : R → K) : List R → K
  | [] => zero
  | r :: rs => plus (f r) (rowSum zero plus f rs)

/-- For each monomial, its incident rows are either all retained or all
    deleted. Hence the root component of a zero identity still sums to zero. -/
theorem component_conservation {R M K : Type} (entry : R → M → K) (zero : K)
    (plus : K → K → K) (zz : plus zero zero = zero) (root : R) (rows : List R)
    (cancels : ∀ m, rowSum zero plus (fun r => entry r m) rows = zero) (m : M) :
    rowSum zero plus (fun r => kept entry zero root r m) rows = zero := by
  classical
  by_cases incident : ∃ u, Connected entry zero root u ∧ entry u m ≠ zero
  · obtain ⟨u, reached, active⟩ := incident
    have pointwise : (fun r => kept entry zero root r m) = (fun r => entry r m) := by
      funext r
      by_cases hr : entry r m = zero
      · simp [kept, hr]
      · simp [kept, Connected.step reached active hr]
    rw [pointwise]
    exact cancels m
  · have pointwise : (fun r => kept entry zero root r m) = (fun _ => zero) := by
      funext r
      by_cases reach : Connected entry zero root r
      · have hr : entry r m = zero := by
          exact Classical.byContradiction (fun hn => incident ⟨r, reach, hn⟩)
        simp [kept, hr]
      · simp [kept, reach]
    rw [pointwise]
    clear cancels
    induction rows with
    | nil => rfl
    | cons r rs ih => simpa [rowSum, ih] using zz

/-- A fiber holds the two coefficients of monomials differing at the
    multiplying variable. Their images add in F2 and paired terms vanish. -/
theorem binary_product_count (fibers : List (Bool × Bool)) :
    countOn Prod.fst fibers + countOn Prod.snd fibers =
      countOn (fun p => xor p.1 p.2) fibers + 2 * countOn (fun p => p.1 && p.2) fibers := by
  induction fibers with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    cases a <;> cases b <;> simp [countOn, weight] at * <;> omega

/-- In other characteristics two nonzero coefficients may merge without
    cancelling. The same one-sided scan charge holds for any unital sum. -/
theorem product_count_bound {K : Type} [DecidableEq K] (zero : K) (plus : K → K → K)
    (leftId : ∀ x, plus zero x = x) (rightId : ∀ x, plus x zero = x)
    (fibers : List (K × K)) :
    countOn (fun p => decide (p.1 ≠ zero)) fibers + countOn (fun p => decide (p.2 ≠ zero)) fibers ≤
    countOn (fun p => decide (plus p.1 p.2 ≠ zero)) fibers +
      2 * countOn (fun p => decide (p.1 ≠ zero ∧ p.2 ≠ zero)) fibers := by
  induction fibers with
  | nil => simp [countOn]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    have one : weight (decide (a ≠ zero)) + weight (decide (b ≠ zero)) ≤
        weight (decide (plus a b ≠ zero)) + 2 * weight (decide (a ≠ zero ∧ b ≠ zero)) := by
      by_cases ha : a = zero <;> by_cases hb : b = zero <;>
        simp [ha, hb, leftId, rightId, weight]
    simp only [countOn]
    omega

end SparseProofSupports
