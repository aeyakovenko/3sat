import Std

namespace SymmetricCubeSlices

/-- Signed contribution of a row to the Laurent exponent. -/
def score (wanted doubled : Bool) : Int :=
  if wanted then (if doubled then 2 else 1) else (if doubled then -2 else -1)

def weight : List Bool → List Bool → Int
  | s :: ss, r :: rs => score s r + weight ss rs
  | _, _ => 0

def misses : List Bool → List Bool → Nat
  | s :: ss, r :: rs => (if s = r then 0 else 1) + misses ss rs
  | _, _ => 0

theorem scoreDeficit (s r : Bool) :
    score s r + (if s = r then 0 else 1) = score s s := by
  cases s <;> cases r <;> decide

theorem weightDeficit (wanted doubled : List Bool) (len : wanted.length = doubled.length) :
    weight wanted doubled + (misses wanted doubled : Int) = weight wanted wanted := by
  induction wanted generalizing doubled with
  | nil => cases doubled <;> simp_all [weight, misses]
  | cons s ss ih =>
    cases doubled with
    | nil => simp at len
    | cons r rs =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      have tail := ih rs len
      cases s <;> cases r <;> simp [score, weight, misses] <;> omega

theorem missesZero (wanted doubled : List Bool) (len : wanted.length = doubled.length)
    (zero : misses wanted doubled = 0) : wanted = doubled := by
  induction wanted generalizing doubled with
  | nil => cases doubled <;> simp_all
  | cons s ss ih =>
    cases doubled with
    | nil => simp at len
    | cons r rs =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      by_cases eq : s = r
      · subst r
        simp [misses] at zero
        rw [ih rs len zero]
      · simp [misses, eq] at zero

theorem uniquePeak (wanted doubled : List Bool) (len : wanted.length = doubled.length)
    (eq : weight wanted doubled = weight wanted wanted) : doubled = wanted := by
  have deficit := weightDeficit wanted doubled len
  have zero : misses wanted doubled = 0 := by omega
  exact (missesZero wanted doubled len zero).symm

/-- Coefficient equations of the column-invariant paired-row perturbation.
Each nontrivial pattern can be realized by a collision on a nonbijective map. -/
theorem forcedWeights {Map Pattern : Type} (plain : Pattern) (hit : Map → Pattern)
    (bij : Map → Bool) (plainOnBij : ∀ t, bij t = true → hit t = plain)
    (existsBij : ∃ t, bij t = true)
    (realize : ∀ p, p ≠ plain → ∃ t, bij t = false ∧ hit t = p)
    (w : Pattern → Int) :
    (∀ t, (if bij t then w plain else 0) + w (hit t) - w plain =
      (if bij t then 1 else 0)) ↔ ∀ p, w p = 1 := by
  constructor
  · intro equations p
    obtain ⟨t, good⟩ := existsBij
    have atPlain := equations t
    simp [good, plainOnBij t good] at atPlain
    by_cases h : p = plain
    · simpa [h] using atPlain
    · obtain ⟨u, bad, reached⟩ := realize p h
      have atHit := equations u
      simp [bad, reached] at atHit
      omega
  · intro constant t
    cases h : bij t <;> simp [constant]

/-- Merging either of two disjoint pairs and then both of them, along with
the bijection equation, fixes the empty weight in the fully symmetric example.
The variables a,b and outside denote sums of singleton deviations. -/
theorem emptyWeight (base a b outside pairA pairB : Int)
    (bij : base + a + b + outside = 1)
    (first : pairA + b + outside = 0) (second : a + pairB + outside = 0)
    (both : pairA + pairB + outside = 0) :
    base = 1 ∧ a + b + outside = 0 := by omega

theorem complementNonzero (base piece other : Int) (plain : base = 1)
    (partition : (piece - base) + (other - base) = 0) :
    piece ≠ 0 ∨ other ≠ 0 := by omega

end SymmetricCubeSlices
