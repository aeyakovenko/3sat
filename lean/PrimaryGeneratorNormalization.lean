import Std

namespace PrimaryGeneratorNormalization

abbrev Bits (n : Nat) := Fin n → Bool
def add (x y : Bits n) : Bits n := fun i => x i ^^ y i

def leads (x : Bits n) (p : Fin n) : Prop :=
  x p = true ∧ ∀ i, i < p → x i = false

/- A reduced quotient space U has no nonzero vector whose first one
   comes after p. The vector with first one at p is then unique. -/
theorem last_pivot_unique (U : Bits n → Prop) (p : Fin n)
    (closed : ∀ x y, U x → U y → U (add x y))
    (detect : ∀ v, U v → (∃ j, v j = true) → ∃ i, i ≤ p ∧ v i = true)
    {x y : Bits n} (hx : U x) (hy : U y) (lx : leads x p) (ly : leads y p) :
    x = y := by
  funext j
  by_cases eq : x j = y j
  · exact eq
  · have hj : add x y j = true := by
      cases h1 : x j <;> cases h2 : y j <;> simp_all [add]
    obtain ⟨i, lo, v⟩ := detect (add x y) (closed _ _ hx hy) ⟨j, hj⟩
    by_cases h : i = p
    · subst i
      simp [add, lx.1, ly.1] at v
    · have lt : i < p := by omega
      simp [add, lx.2 i lt, ly.2 i lt] at v

/- h = length - shift is the level of a primary-basis column. Columns
   in the image N ker(N^(r+1)) are precisely shifted columns of
   height at most r; their predecessors have height one larger. -/
theorem predecessor_level {len t r : Nat} (ht : 0 < t) (valid : t < len) :
    (len - (t - 1) ≤ r + 1) ↔ (len - t ≤ r) := by omega

theorem top_quotient_layer {len t r : Nat} (valid : t < len) :
    ((len - t ≤ r) ∧ ¬ ((len - t < r) ∨ (0 < t ∧ len - t ≤ r))) ↔
    (len = r ∧ t = 0) := by omega

/- If the image of a candidate set of cyclic generators spans the
   quotient by N, nilpotence lifts generation to the entire module.
   S expresses membership in the generated submodule. -/
theorem lift_from_quotient {V : Type} (S : V → Prop) (N : V → V)
    (plus : V → V → V) (zero : V)
    (closed : ∀ x y, S x → S y → S (plus x y))
    (stable : ∀ x, S x → S (N x))
    (dist : ∀ x y, N (plus x y) = plus (N x) (N y))
    (assoc : ∀ x y z, plus (plus x y) z = plus x (plus y z))
    (rightZero : ∀ x, plus x zero = x)
    (onto : ∀ x, ∃ s y, S s ∧ x = plus s (N y))
    (iter : Nat → V → V)
    (iterZero : ∀ x, iter 0 x = x)
    (iterSucc : ∀ k x, iter (k+1) x = N (iter k x))
    (nilp : ∃ k, ∀ x, iter k x = zero) : ∀ x, S x := by
  have shift : ∀ k x, ∃ s y, S s ∧ iter k x = plus s (iter (k+1) y) := by
    intro k
    induction k with
    | zero =>
      intro x
      obtain ⟨s, y, hs, h⟩ := onto x
      exact ⟨s, y, hs, by simpa [iterZero,iterSucc] using h⟩
    | succ k ih =>
      intro x
      obtain ⟨s, y, hs, he⟩ := ih x
      exact ⟨N s, y, stable s hs, by rw [iterSucc k x, he, dist, iterSucc (k+1) y]⟩
  have form : ∀ k x, ∃ s y, S s ∧ x = plus s (iter (k+1) y) := by
    intro k
    induction k with
    | zero =>
      intro x
      simpa [iterZero] using shift 0 x
    | succ k ih =>
      intro x
      obtain ⟨s, y, hs, he⟩ := ih x
      obtain ⟨u, z, hu, hz⟩ := shift (k+1) y
      exact ⟨plus s u, z, closed _ _ hs hu, by rw [he,hz,assoc]⟩
  intro x
  obtain ⟨k, hk⟩ := nilp
  obtain ⟨s, y, hs, he⟩ := onto x
  cases k with
  | zero => have hy : N y = zero := by simpa [iterZero] using hk (N y)
            simpa [he, hy, rightZero] using hs
  | succ k =>
    obtain ⟨u, z, hu, hz⟩ := form k x
    simpa [hz, hk z, rightZero] using hu

end PrimaryGeneratorNormalization
