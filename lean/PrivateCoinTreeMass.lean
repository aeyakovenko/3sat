import Std

namespace PrivateCoinTreeMass

/-- Deepest depth first, with all counts in units of the deepest leaf. -/
def value : List Nat → Nat
  | [] => 0
  | n :: rest => n + 2 * value rest

/-- Normalize a histogram, propagating one carry at a time to shallower depths. -/
def normalize (incoming : Nat) : List Nat → List Nat
  | [] => [incoming]
  | n :: rest => (incoming + n) % 2 :: normalize ((incoming + n) / 2) rest

theorem normalize_value (counts : List Nat) (incoming : Nat) :
    value (normalize incoming counts) = incoming + value counts := by
  induction counts generalizing incoming with
  | nil => simp [normalize, value]
  | cons n rest ih =>
    simp only [normalize, value]
    rw [ih]
    omega

/-- The deepest D normalized digits can contribute less than one root unit.
    The digits use little-endian order in units of the deepest leaf. -/
theorem fractional_digits_lt (digits : List Nat) (bits : ∀ n ∈ digits, n < 2) :
    value digits < 2 ^ digits.length := by
  induction digits with
  | nil => simp [value]
  | cons n rest ih =>
    have hn := bits n (List.mem_cons_self ..)
    have ht := ih (fun m hm => bits m (List.mem_cons_of_mem _ hm))
    simp only [value, List.length_cons, Nat.pow_succ]
    omega

end PrivateCoinTreeMass
