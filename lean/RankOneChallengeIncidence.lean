import Std

namespace RankOneChallengeIncidence

/-- List of incidences in the chosen order of the row spaces. -/
def hits : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + hits rest

/-- Each set hit at position i contributes 2^i. -/
def weight : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * weight rest

theorem incidence (bs : List Bool) : 2 ^ hits bs ≤ 1 + weight bs := by
  induction bs with
  | nil => decide
  | cons b rest ih =>
    cases b with
    | false =>
      simp [hits, weight]
      omega
    | true =>
      simp only [hits, weight, if_true, Nat.pow_add, Nat.pow_one]
      omega

/-- Summation over any finite enumeration of nonzero column challenges. -/
theorem total {X : Type} (vectors : List X) (profile : X → List Bool) :
    (vectors.map fun v => 2 ^ hits (profile v) - 1).sum ≤
    (vectors.map fun v => weight (profile v)).sum := by
  induction vectors with
  | nil => simp
  | cons v rest ih =>
    have hv := incidence (profile v)
    simp only [List.map_cons, List.sum_cons]
    omega

end RankOneChallengeIncidence
