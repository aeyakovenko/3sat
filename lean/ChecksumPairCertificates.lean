import Std

namespace ChecksumPairCertificates

def parity : List Bool → Bool
  | [] => false
  | b :: rest => b.xor (parity rest)

theorem permuteFour :
    ∀ a b c d : Bool, (a.xor b).xor (c.xor d) = (a.xor c).xor (b.xor d) := by decide

theorem parityAdd {α : Type} (rows : List α) (f g : α → Bool) :
    parity (rows.map fun x => (f x).xor (g x)) =
    (parity (rows.map f)).xor (parity (rows.map g)) := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    simpa only [List.map_cons, parity, ih] using
      permuteFour (f a) (g a) (parity (rows.map f)) (parity (rows.map g))

theorem combineConstant : ∀ a b c : Bool,
    (a && c).xor (b && c) = ((a.xor b) && c) := by decide

theorem parityBit {α : Type} (rows : List α) (f : α → Bool) (bit : Bool) :
    parity (rows.map fun x => f x && bit) = (parity (rows.map f) && bit) := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    simpa only [List.map_cons, parity, ih] using combineConstant (f a) (parity (rows.map f)) bit

/-- The nonconstant contributions to the certified line equations cancel,
and the remaining common-bit coefficient occurs with odd parity. -/
theorem witnessedMoment {α : Type} (rows : List α) (constant residual : α → Bool)
    (bit : Bool) (annihilated : parity (rows.map residual) = false)
    (odd : parity (rows.map constant) = true) :
    parity (rows.map fun x => ((constant x && bit).xor (residual x))) = bit := by
  rw [parityAdd, parityBit, annihilated, odd]
  cases bit <;> rfl

/-- The signed excess of even pairs of two independent sign lists factors. -/
theorem pairExcess (a b c d : Int) :
    (a*c + b*d) - (a*d + b*c) = (a-b)*(c-d) := by
  simp only [Int.sub_mul, Int.mul_sub]
  omega

end ChecksumPairCertificates
