import QuadraticDefs
namespace CycleImageQuadratic
theorem no_five : atDepth imageWords 5 = false := by native_decide
def sixBitImage : Array Nat :=
  #[5,15,21,22,25,27,28,31,34,41,42,45,51,52,53,59]

theorem no_five_after_second_map : atDepth sixBitImage 5 6 = false := by native_decide
end CycleImageQuadratic
