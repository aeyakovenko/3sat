import Std

namespace SemanticCutPermutations

/-- A fixed local half and privately chosen native cut can be compiled into
a tree of remote coordinate reads. A terminal can carry the entire local log. -/
inductive Queries (Index Value Result : Type) where
  | done (result : Result)
  | ask (index : Index) (next : Value → Queries Index Value Result)

def observe (tree : Queries I V R) (input : I → V) : List (I × V) × R :=
  match tree with
  | .done r => ([], r)
  | .ask i next =>
    let tail := observe (next (input i)) input
    ((i, input i) :: tail.1, tail.2)

theorem observe_agrees (tree : Queries I V R) (x y : I → V)
    (agree : ∀ i v, (i, v) ∈ (observe tree x).1 → x i = y i) :
    observe tree x = observe tree y := by
  induction tree with
  | done r => rfl
  | ask i next ih =>
    have same : x i = y i := agree i (x i) (by simp [observe])
    have ht := ih (x i) (fun j v hj => agree j v (by simp [observe, hj]))
    simp only [observe, ← same, ht]

/-- On the mixed pair (p,q), the prefix of p and the replacement for q
glue. Verdict preservation for the first cut forces equality. -/
theorem mixed_diagonals (p q : I → V) (leftPrefix : Queries I V R)
    (rightSuffix : (I → V) → Queries I V Bool)
    (prefixAgree : ∀ i v, (i, v) ∈ (observe leftPrefix p).1 → p i = q i)
    (suffixAgree : ∀ i v, (i, v) ∈ (observe (rightSuffix q) q).1 → q i = p i)
    (preserves : ∀ y, observe leftPrefix p = observe leftPrefix y →
      (observe (rightSuffix y) p).2 = false → p = y)
    (rejects : (observe (rightSuffix q) q).2 = false) : p = q := by
  apply preserves q (observe_agrees leftPrefix p q prefixAgree)
  rw [← observe_agrees (rightSuffix q) q p suffixAgree]
  exact rejects

/-- Existential Boolean colors witness precisely a disagreement of the two
lists, including when they happen to be permutations. -/
def hasMismatch (p q : I → V) : Prop :=
  ∃ (w : V → Bool) (z : I → Bool), (∀ i, z i = w (p i)) ∧ ∃ i, z i ≠ w (q i)

theorem hasMismatch_iff (p q : I → V) : hasMismatch p q ↔ p ≠ q := by
  classical
  constructor
  · rintro ⟨w, z, leftEq, i, wrong⟩ same
    subst q
    exact wrong (leftEq i)
  · intro different
    have diffAt : ∃ i, p i ≠ q i := by
      apply Classical.byContradiction
      intro h
      apply different
      funext i
      exact Classical.byContradiction (fun hi => h ⟨i, hi⟩)
    obtain ⟨index, ne⟩ := diffAt
    let w : V → Bool := fun v => decide (v = p index)
    exact ⟨w, fun i => w (p i), fun _ => rfl, index, by simp [w, Ne.symm ne]⟩

/-- The gain from ordering a pair of values in the same direction as a
pair of weights is the product of their two positive gaps. -/
theorem swap_score (i di v dv : Nat) :
    i * v + (i + di) * (v + dv) = i * (v + dv) + (i + di) * v + di * dv := by
  simp only [Nat.add_mul, Nat.mul_add]
  omega

end SemanticCutPermutations
