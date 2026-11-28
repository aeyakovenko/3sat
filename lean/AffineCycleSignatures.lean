import Std

namespace AffineCycleSignatures

def cover (n x : Nat) : Bool :=
  (List.range n).all fun i => x.testBit i || x.testBit ((i+1) % n)

def parityOn (n s x : Nat) : Bool :=
  (List.range n).foldl (fun p i => p != (s.testBit i && x.testBit i)) false

def slice (n normal : Nat) (bias : Bool) : List Nat :=
  (List.range (2^n)).filter fun x => cover n x && (parityOn n normal x == bias)

def sizeOfCoverSet (n : Nat) : Nat :=
  ((List.range (2^n)).filter (cover n)).length

def eligible (n normal : Nat) (bias : Bool) : Bool :=
  (normal != 0) && ((slice n normal bias).length == sizeOfCoverSet (n-1))

def triple (n s : Nat) : Bool :=
  (List.range n).any fun i =>
    s == (2^i + 2^((i+1)%n) + 2^((i+2)%n))

def opposite (s : Nat) : Bool :=
  (List.range 4).any fun i => s == (2^i + 2^(i+4))

theorem six_classification : ∀ s : Fin 64, ∀ b : Bool,
    eligible 6 s.val b =
      ((triple 6 s.val && !b) || ((s.val == 21 || s.val == 42) && b)) := by
  native_decide

theorem seven_classification : ∀ s : Fin 128, ∀ b : Bool,
    eligible 7 s.val b = (triple 7 s.val && !b) := by native_decide

theorem eight_classification : ∀ s : Fin 256, ∀ b : Bool,
    eligible 8 s.val b = ((triple 8 s.val || opposite s.val) && !b) := by
  native_decide

def centroid (l : List Nat) : Nat := l.foldl Nat.xor 0

theorem exceptional_centroids :
    centroid ((List.range 32).filter (cover 5)) = 0 ∧
    cover 5 0 = false ∧
    centroid (slice 6 21 true) = 63 ∧ centroid (slice 6 42 true) = 63 ∧
    cover 6 63 = true := by native_decide

theorem exceptional_eight_split :
    ((slice 8 17 false).filter (fun x => !x.testBit 0)).length = 4 ∧
    ((slice 8 17 false).filter (fun x => x.testBit 0)).length = 25 := by
  native_decide

end AffineCycleSignatures
