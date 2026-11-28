import SevenImageDefs

namespace QuadraticFixedChain

private def first : Array Nat := #[9,14,26,30,16,10,6,0,7,12,3,0,12,0,0,0]
def second : Array Nat :=
  #[8,43,49,42,28,48,54,0,1,16,60,0,52,0,0,0,6,21,33,0,11,0,0,0,29,0,0,0,0,0,0,0]
def third : Array Nat := #[4,5,2,0,12,0,0,0,20,4,4,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

def poly (a : Array Nat) (x : Nat) : Nat := (List.range a.size).foldl
  (fun acc s => if (s &&& x) == s then acc ^^^ a[s]! else acc) 0

def six : Array Nat := #[10,15,21,26,27,30,31,33,34,42,47,50,56,58,60,62]
def seven : Array Nat := #[22,27,45,54,55,58,59,65,70,86,91,102,112,118,122,124]

private def weight (s : Nat) := ((List.range 6).filter (fun i => s.testBit i)).length

def exactQuadratic (a : Array Nat) : Bool :=
  (List.range a.size).all (fun m => weight m ≤ 2 || a[m]! == 0) &&
  (List.range a.size).any (fun m => weight m == 2 && a[m]! != 0)

def valid (n : Nat) (f : Nat → Nat) : Bool :=
  (List.range (2^n)).all (fun x => f x < 2^(n+1) &&
    CycleImageClock.cover n x == CycleImageClock.cover (n+1) (f x)) &&
  ((List.range (2^n)).map f).eraseDups.length == 2^n

/-- If chosen, the correction changes the inserted bit exactly when x₃ = 0
and x₀ = x₁. All six original coordinates occupy their original cyclic order. -/
def insertBit (useCorrection : Bool) (x : Nat) : Nat :=
  let correction := useCorrection && !x.testBit 3 && (x.testBit 0 == x.testBit 1)
  let inserted := (x.testBit 1 != x.testBit 2) != correction
  x%4 + 4*inserted.toNat + 8*(x/4)

theorem exact_degrees : [first,second,third].all exactQuadratic = true := by native_decide

theorem valid_on_complete_cubes :
    valid 4 (poly first) ∧ valid 5 (poly second) ∧ valid 6 (poly third) ∧
    valid 6 (insertBit false) := by native_decide

theorem third_is_corrected_insertion : ∀ x : Fin 64,
    poly third x = insertBit true x := by native_decide

theorem unchanged_on_selected_six : six.all (fun x =>
    poly third x == insertBit false x) = true := by native_decide

theorem inherited_images :
    ((List.range 16).map (fun x => poly second (poly first x))).mergeSort = six.toList ∧
    (six.toList.map (poly third)).mergeSort = seven.toList := by native_decide

/-- Repeat a selected row to fill any unused lanes. Numerical upper bounds
come from the existing programs on the complete six- and seven-bit catalogs. -/
def boundedSearch (n : Nat) (suite : Array Nat) (fuel : Nat) : Bool := Id.run do
  let rows := fun i => suite[i]?.getD suite[0]!
  let constants := (List.range 8).toArray.map fun k => SevenImageSearch.encode 3 (fun _ => k)
  let mem := (List.range 8).toArray.map fun j =>
    SevenImageSearch.encode 3 (fun i => ((rows i) >>> (3*j)) % 8)
  let mut target : SevenImageSearch.Cut := 0
  for i in [:21] do
    if CycleImageClock.cover n (rows i) then target := target ||| (1 <<< i.toUInt64)
  return ((SevenImageSearch.search constants target fuel SevenImageSearch.allRows #[] mem).run {}).1

theorem midpoint_excludes_five : boundedSearch 6 six 5 = false := by native_decide

theorem endpoint_excludes_six : boundedSearch 7 seven 6 = false := by native_decide

end QuadraticFixedChain
