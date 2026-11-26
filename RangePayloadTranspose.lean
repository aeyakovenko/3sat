import Std

namespace RangePayloadTranspose

def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

def gather : List Bool → List Int → List Int
  | true :: ms, a :: as => a :: gather ms as
  | false :: ms, _ :: as => gather ms as
  | _, _ => []

def deposit : List Bool → List Int → List Int
  | [], _ => []
  | false :: ms, bs => 0 :: deposit ms bs
  | true :: ms, [] => 0 :: deposit ms []
  | true :: ms, b :: bs => b :: deposit ms bs

theorem stable_transpose (mask : List Bool) (xs ys : List Int) :
    dot (gather mask xs) ys = dot xs (deposit mask ys) := by
  induction mask generalizing xs ys with
  | nil => cases xs <;> simp [gather, deposit, dot]
  | cons m ms ih =>
    cases xs with
    | nil => simp [gather, dot]
    | cons a as =>
      cases m <;> cases ys <;> simp [gather, deposit, dot, ← ih]

def prefixSum : Nat → List Int → Int
  | n + 1, x :: xs => x + prefixSum n xs
  | _, _ => 0

/-- The difference between endpoints marks exactly this first segment.
Trailing implicit zeroes need no entries in the dot product. -/
theorem prefix_transpose (r : Nat) (xs : List Int) (w : Int) :
    dot xs (List.replicate r w) = prefixSum r xs * w := by
  induction r generalizing xs with
  | zero => cases xs <;> simp [dot, prefixSum]
  | succ r ih =>
    cases xs <;> simp [dot, prefixSum, ih, List.replicate_succ, Int.add_mul]

end RangePayloadTranspose
