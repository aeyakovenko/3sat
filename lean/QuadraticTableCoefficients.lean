import Std

namespace QuadraticTableCoefficients

/-- The first component is a signed coefficient, the second its unnormalized
    correlation. Multiplying by a common denominator permits rational weights. -/
theorem weightedCorrelation (terms : List (Int × Int)) (bound : Nat)
    (bounded : ∀ t ∈ terms, t.2.natAbs ≤ bound) :
    ((terms.map (fun (t : Int × Int) => t.1 * t.2)).sum).natAbs ≤
      (terms.map (fun (t : Int × Int) => t.1.natAbs)).sum * bound := by
  induction terms with
  | nil => simp
  | cons t rest ih =>
    have ht := bounded t (by simp)
    have tail := ih (fun u hu => bounded u (by simp [hu]))
    simp only [List.map_cons, List.sum_cons, Nat.add_mul]
    apply Nat.le_trans (Int.natAbs_add_le _ _)
    rw [Int.natAbs_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ ht) tail

/-- Averaging the translated derivatives of a sign yields its signed bias
    times the original sign, with the normalizing denominator cleared. -/
theorem translateMixture (sign : Int) (values : List Int) (shifted : List Int)
    (shift : shifted.Perm values) :
    (shifted.map (fun v => sign * v)).sum = sign * values.sum := by
  have hp : shifted.sum = values.sum := by
    induction shift with
    | nil => rfl
    | cons a _ ih => simp [ih]
    | swap => simp [Int.add_left_comm]
    | trans _ _ h k => exact h.trans k
  rw [← hp]
  clear shift hp
  induction shifted with
  | nil => simp
  | cons a rest ih => simp [ih, Int.mul_add]

/-- The two correlation bounds, before squaring and dividing by support size,
    imply the normalized overlap bound even for a very small support. -/
theorem supportedOverlap (cross support bias : Nat)
    (bySupport : cross ≤ support) (byBias : cross ≤ bias) :
    cross * cross ≤ support * bias :=
  Nat.mul_le_mul bySupport byBias

/-- At intermediate support density, multiply each derivative contribution
    by four. The identity contributes at most four, the other core shifts at
    most two, and all remaining shifts at most one. -/
theorem middleSupport (coreOthers outside : Nat) (many : 2 < outside) :
    4 + 2 * coreOthers + outside < 2 * (1 + coreOthers + outside) := by
  omega

end QuadraticTableCoefficients
