import SevenImageDefs
import CompleteSevenCycleClock

namespace SevenImageSearch

def compactSuite : Array Nat := #[22,29,35,53,54,59,62,70,77,83,85,86,93,123,124,126]
theorem compact_outside_gap0 : compactSuite.filter (fun v => !inXorImage v) = #[124] := by decide +kernel
theorem compact_cover_count : (compactSuite.filter cover).size = 7 := by decide +kernel

/-- Repeat the first row to fill all 21 lanes in the native census. -/
def compactAtDepth (fuel : Nat) : Bool := Id.run do
  let rows := fun i => compactSuite[i]?.getD 22
  let constants := (List.range 8).toArray.map fun k => encode 3 (fun _ => k)
  let mem := (List.range 8).toArray.map fun j => encode 3 (fun i => ((rows i) >>> (3*j)) % 8)
  let mut target : Cut := 0
  for i in [:21] do if cover (rows i) then target := target ||| (1 <<< i.toUInt64)
  return ((search constants target fuel allRows #[] mem).run {}).1

theorem compact_exclude_six : compactAtDepth 6 = false := by native_decide

/-- The rows passed to the six-step census are exactly the composed image of
    the original sixteen masks, checked across the two modules. -/
theorem same_ancestors_and_failed_census :
    CompleteSevenCycleClock.FixedSixteen.sortedAncestralOutputs = compactSuite.toList ∧
      compactAtDepth 6 = false :=
  ⟨CompleteSevenCycleClock.FixedSixteen.composed_image.trans (by decide +kernel),
    compact_exclude_six⟩

end SevenImageSearch
