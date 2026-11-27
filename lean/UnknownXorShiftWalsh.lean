import MatrixTriangleWalsh

namespace UnknownXorShiftWalsh

open MatrixTriangleWalsh

def xorWord : {n : Nat} → Word n → Word n → Word n
  | 0, .nil, .nil => .nil
  | _+1, .cons a x, .cons b y => .cons (a ^^ b) (xorWord x y)

theorem character_xor {n} (x a b : Word n) :
    character x (xorWord a b) = character x a * character x b := by
  induction x with
  | nil => cases a; cases b; decide
  | cons e x ih =>
    cases a with
    | cons f a =>
      cases b with
      | cons g b =>
        cases e <;> cases f <;> cases g <;>
          simp [xorWord, character, ih, Int.neg_mul, Int.mul_neg]

/-- The (i,j) entry of H diag(character s) H as an integer,
so the identity may also be reduced modulo five. -/
theorem hidden_shift_entry {n} (i j s : Word n) :
    total n (fun u => (character u i * character u s) * character u j) =
      if xorWord i s = j then (2:Int)^n else 0 := by
  simpa only [character_xor] using orthogonal (xorWord i s) j

#print axioms hidden_shift_entry

end UnknownXorShiftWalsh
