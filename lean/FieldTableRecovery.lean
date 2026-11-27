import Std

namespace FieldTableRecovery

/-- Field entries are represented in the polynomial basis with
u⁴ = 1+u+u²+u³. -/
abbrev F := BitVec 4

def mulU (z : F) : F := if z.msb then (z <<< 1) ^^^ 15 else z <<< 1

def shifted (twice : Bool) (z : F) := if twice then mulU (mulU z) else mulU z

/-- The normalized pair of observations determines both contributions,
including when the optional contribution is zero. -/
theorem separate_tag (twice : Bool) (x y x' y' : F)
    (base : x ^^^ y = x' ^^^ y')
    (more : x ^^^ shifted twice y = x' ^^^ shifted twice y') :
    x = x' ∧ y = y' := by
  have nonsing : ∀ (b : Bool) (a a' : F),
      a ^^^ shifted b a = a' ^^^ shifted b a' → a = a' := by decide
  have dir : y ^^^ shifted twice y = y' ^^^ shifted twice y' := by
    generalize h : shifted twice y = v at more ⊢
    generalize h' : shifted twice y' = w at more ⊢
    bv_decide
  obtain rfl := nonsing twice y y' dir
  exact ⟨by bv_decide, rfl⟩

def baseExponent (c : Fin 5) : Nat := if c.val = 4 then 2 else 1

def nextExponent (c : Fin 5) : Nat := (baseExponent c + c.val) % 5

theorem good_exponents :
    ∀ c : Fin 5, 0 < baseExponent c ∧ baseExponent c < 5 ∧
      0 < nextExponent c ∧ nextExponent c < 5 ∧
      (nextExponent c + 5 - baseExponent c) % 5 = c.val := by decide

theorem good_shifts :
    ∀ e : Fin 5, e.val > 0 →
      let g := if e.val = 4 then 2 else 1
      0 < (e.val + g) % 5 ∧ 0 < g ∧ g < 5 := by decide

/-- Each distinct four-query pair containing an error accounts for an
erroneous query. A bad field point has at least one-quarter bad inner digits. -/
theorem field_point_account (badPoints encodedPoints alphabet totalErrors : Nat)
    (quarter : badPoints * alphabet ≤ 4 * totalErrors)
    (accuracy : 1024 * totalErrors ≤ 4 * (encodedPoints * alphabet))
    (positive : 0 < alphabet) : 64 * badPoints ≤ encodedPoints := by
  have step : 256 * (badPoints * alphabet) ≤ 4 * (encodedPoints * alphabet) := by omega
  have scaled : (64 * badPoints) * alphabet ≤ encodedPoints * alphabet := by
    rw [Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_right scaled positive

theorem unique_line_room (q d : Nat) (large : 8 * (d + 1) ≤ q) :
    d + (q - 1) / 4 < q - 1 - (q - 1) / 4 := by omega

/-- The nonzero sampling determinant in the prime field at all pairs
of distinct nonzero parameters. Extension-field independence uses the
same determinant identity as in the manuscript. -/
theorem curve_determinants_five : ∀ t s : Fin 5,
    t ≠ 0 → s ≠ 0 → t ≠ s → t * s * (s - t) ≠ 0 := by decide

/-- At scalar minus one in the five-element field, a single padded
hole carries its Boolean challenge in the exponent modulo four. -/
theorem fixed_scalar_binary_value : ∀ b : Fin 2,
    (6 - (2 ^ (2 * b.val)) % 5) % 5 = 2 * b.val := by decide

theorem binary_padding_period : (2 : Nat) ^ 4 % 5 = 1 := by decide

end FieldTableRecovery
