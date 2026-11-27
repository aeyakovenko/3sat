import Std

namespace QuadraticFibers

def sign (b : Bool) : Int := if b then -1 else 1

/-- Summing a quadratic character over one interacting pair eliminates both
variables. The two linear coefficients can depend on every remaining bit. -/
theorem eliminatePair (a b c : Bool) :
    sign c + sign (b ^^ c) + sign (a ^^ c) +
        sign (true ^^ a ^^ b ^^ c) = 2 * sign ((a && b) ^^ c) := by
  cases a <;> cases b <;> cases c <;> decide

def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

def character : List Bool → List Bool → Int
  | a :: as, b :: bs => sign (a && b) * character as bs
  | _, _ => 1

private theorem negSum (xs : List Int) : (xs.map Neg.neg).sum = -xs.sum := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]; omega

private theorem appendSum (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_assoc]

/-- The complete character sum detects whether a bit vector is zero. This is
the orthogonality identity used to recover an exact output histogram. -/
theorem orthogonality (bs : List Bool) :
    ((masks bs.length).map (fun a => character a bs)).sum =
      if bs.contains true then 0 else (2 : Int) ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b with
    | false =>
      simp [masks, List.map_append, List.map_map, Function.comp_def, character,
        sign, appendSum, ih, Int.pow_succ]
      split <;> omega
    | true =>
      have hn : ((masks bs.length).map (fun a => -(character a bs))).sum =
          -((masks bs.length).map (fun a => character a bs)).sum := by
        simpa [List.map_map, Function.comp_def] using
          negSum ((masks bs.length).map (fun a => character a bs))
      simp [masks, List.map_append, List.map_map, Function.comp_def, character,
        sign, appendSum, hn]
      omega

end QuadraticFibers
