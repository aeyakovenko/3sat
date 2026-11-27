import Std

/-! Local ternary measurements for the weights 3, 2, 1 and for pairs of unit bits. -/
namespace ChargeAffineMeasurements

def packBit (b : Bool) : Fin 3 := if b then 1 else 0

def twoReadings (x y z : Bool) : Fin 3 × Fin 3 :=
  (packBit x - packBit z, packBit y - packBit z)

def charge (x y z : Bool) : Nat :=
  (3 * x.toNat + 2 * y.toNat + z.toNat) % 6

theorem readingsDetermineCharge :
    ∀ x y z x' y' z' : Bool, twoReadings x y z = twoReadings x' y' z' →
      charge x y z = charge x' y' z' := by decide

theorem pairSumIsExact :
    ∀ x y : Bool, (packBit x + packBit y).val = x.toNat + y.toNat := by decide

end ChargeAffineMeasurements
