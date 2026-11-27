import Std

/-! The seven gaps are encoded little-endian. A set bit represents increment minus one. -/
namespace SevenTileIsolation

abbrev F := Fin 3

def step (s : BitVec 7) (i : Nat) : F := if s.getLsbD i then 2 else 1

def base (s : BitVec 7) : Nat → F
  | 0 => 0
  | i+1 => base s i + step s i

def tip (s : BitVec 7) (i : Nat) := base s i - step s i

def order : List Nat := [1,4,3,5,6,0,2]

def valid (s : BitVec 7) : Bool :=
  (order.zip order.tail).all (fun ij => tip s ij.1 != tip s ij.2)

/-- Theta is chosen by the first bit. The last two bits independently specify the port difference. -/
theorem signs_exact : ∀ s : BitVec 7, valid s = true ↔
    step s 1 = step s 0 ∧ step s 2 = 0-step s 0 ∧ step s 3 = step s 0 ∧
    step s 4 = step s 0 ∧ step s 6 = step s 5 := by decide

/-- Every raw colour, after normalizing the tile's starting colour to zero. -/
theorem colors_exact : ∀ s : BitVec 7, valid s = true →
    let t := step s 0
    let d := base s 7
    ((List.range 8).map (base s) = [0,t,0-t,t,0-t,0,0-d,d] ∧
      (List.range 7).map (tip s) = [0-t,0,0,0,t,d,0] ∧
      d ≠ 0 ∧ step s 5 = 0-d) := by decide

theorem four_codes : (List.range 128).filter (fun n => valid (BitVec.ofNat 7 n)) =
    [4,27,100,123] := by decide

theorem switches : ∀ s : BitVec 7, valid s = true →
    valid (s ^^^ 31) = true ∧ valid (s ^^^ 96) = true ∧
    base (s ^^^ 31) 7 = base s 7 ∧ base (s ^^^ 96) 7 = 0-base s 7 ∧
    step (s ^^^ 31) 0 = 0-step s 0 ∧ step (s ^^^ 96) 0 = step s 0 := by decide

end SevenTileIsolation
