import Std

namespace QuadraticFiveToSixWitness

def coeff : List Nat :=
  [60,48,50,34,44,47,6,0,46,52,51,0,10,0,0,0,31,25,51,0,55,0,0,0,21,0,0,0,0,0,0,0]

def mapWord (x : Nat) : Nat :=
  ((List.range coeff.length).filter fun s => (x &&& s) == s).foldl
    (fun a s => a ^^^ coeff[s]!) 0

def cover (n x : Nat) : Bool :=
  (List.range n).all fun i => x.testBit i || x.testBit ((i+1)%n)

def bitWeight (s : Nat) : Nat :=
  ((List.range 5).filter fun i => s.testBit i).length

def source : List Nat := [9,7,19,3,25,29,5,31,14,12,23,11,18,26,13,27]
def target : List Nat := [5,15,21,22,25,27,28,31,34,41,42,45,51,52,53,59]

theorem valid : ∀ x : Fin 32, mapWord x.val < 64 ∧ cover 6 (mapWord x.val) = cover 5 x.val := by
  native_decide

theorem injective : ∀ x y : Fin 32, mapWord x.val = mapWord y.val → x = y := by
  native_decide

theorem quadratic : ∀ i : Fin 6,
    (∀ s : Fin 32, (coeff[s.val]!).testBit i.val → bitWeight s.val ≤ 2) ∧
    (∃ s : Fin 32, (coeff[s.val]!).testBit i.val ∧ bitWeight s.val = 2) := by
  have upper : ∀ i : Fin 6, ∀ s : Fin 32,
      (coeff[s.val]!).testBit i.val → bitWeight s.val ≤ 2 := by native_decide
  have hits : ∀ i : Fin 6, (List.finRange 32).any (fun s =>
      (coeff[s.val]!).testBit i.val && (bitWeight s.val == 2)) = true := by native_decide
  intro i
  refine ⟨upper i, ?_⟩
  obtain ⟨s, _, h⟩ := List.any_eq_true.mp (hits i)
  exact ⟨s, by simpa using h⟩

theorem exactImage : (source.map mapWord).mergeSort = target := by native_decide

end QuadraticFiveToSixWitness
