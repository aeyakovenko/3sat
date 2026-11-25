import Std

namespace PrivateRowsOfAffineInjections

abbrev Table (Index Bit : Type) := Index → Bit → Bool

def mix {I B : Type} (c p q : Table I B) : Table I B :=
  fun i j => (c i j ^^ p i j) ^^ q i j

def RowChoice {I B : Type} (family : Table I B → Prop) (base : Table I B)
    (i : I) (value : B → Bool) : Prop :=
  ∃ p, family p ∧ p i = value ∧ ∀ j, j ≠ i → p j = base j

private theorem cancelFirst (a b : Bool) : ((a ^^ a) ^^ b) = b := by
  cases a <;> cases b <;> decide

private theorem cancelLast (a b : Bool) : ((a ^^ b) ^^ a) = b := by
  cases a <;> cases b <;> decide

/-- The sets of labels available while all other rows stay at the base table are disjoint. -/
theorem privateRowValuesAreDisjoint {I B : Type} (family : Table I B → Prop)
    (closed : ∀ c p q, family c → family p → family q → family (mix c p q))
    (injective : ∀ p, family p → ∀ i j, p i = p j → i = j)
    {base : Table I B} (valid : family base) {i j : I} (different : i ≠ j)
    {v : B → Bool} (left : RowChoice family base i v) :
    ¬ RowChoice family base j v := by
  rintro ⟨q, hq, qj, qfixed⟩
  obtain ⟨p, hp, pi, pfixed⟩ := left
  have atI : mix base p q i = v := by
    funext b
    simp only [mix, qfixed i different, pi]
    exact cancelLast _ _
  have atJ : mix base p q j = v := by
    funext b
    simp only [mix, pfixed j (Ne.symm different), qj]
    exact cancelFirst _ _
  exact different ((injective _ (closed base p q valid hp hq)) i j (atI.trans atJ.symm))

/-- The rank bound obtained by iterating a deletion that costs at most log₂(Q/t).
The linear-algebra dimension and finite cardinality hypotheses are the manuscript steps. -/
def capacity (q : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => capacity q t + (q / (t+1)).log2

theorem deletionBound {q : Nat} (rankPossible : Nat → Nat → Prop)
    (empty : ∀ r, rankPossible 0 r → r = 0)
    (delete : ∀ t r, rankPossible (t+1) r →
      ∃ r', rankPossible t r' ∧ r ≤ r' + (q / (t+1)).log2) :
    ∀ t r, rankPossible t r → r ≤ capacity q t := by
  intro t
  induction t with
  | zero =>
    intro r hr
    simp [capacity, empty r hr]
  | succ t ih =>
    intro r hr
    obtain ⟨r', h', hle⟩ := delete t r hr
    exact Nat.le_trans hle (Nat.add_le_add_right (ih r' h') _)

end PrivateRowsOfAffineInjections
