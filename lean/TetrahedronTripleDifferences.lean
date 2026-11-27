import Std

namespace TetrahedronTripleDifferences

inductive Letter | zero | left | right | both
  deriving DecidableEq, Repr

def all : List Letter := [.zero, .left, .right, .both]

/-- The two operands and the output of one Boolean multiplication. -/
def gate : Letter → Bool × Bool × Bool
  | .zero => (false, false, false)
  | .left => (true, false, false)
  | .right => (false, true, false)
  | .both => (true, true, true)

def edge (x y : Letter) : Bool × Bool × Bool :=
  let a := gate x
  let b := gate y
  (a.1 ^^ b.1, a.2.1 ^^ b.2.1, a.2.2 ^^ b.2.2)

def triples : List (Letter × Letter × Letter) :=
  all.flatMap (fun x => all.flatMap (fun y => all.map (fun z => (x, y, z))))

def observation (t : Letter × Letter × Letter) :=
  (edge t.1 t.2.1, edge t.1 t.2.2)

/-- The logarithm in base two of the number of preimages of the observation. -/
def charge (x y z : Letter) : Nat :=
  if x = y ∧ x = z then 2 else if x = y ∨ x = z ∨ y = z then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem fiberSize (x y z : Letter) :
    (triples.filter (fun t => observation t == observation (x, y, z))).length =
      2 ^ charge x y z := by
  cases x <;> cases y <;> cases z <;> decide

/-- Eleven bits of fiber charge per sixteen equally likely triples. -/
theorem uniformCharge : (triples.map (fun t => charge t.1 t.2.1 t.2.2)).sum = 44 := by
  decide

private theorem squareNonneg (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- Tangent inequality for `3p²−p³` at `p=1/4`, with denominator `n`.
    Four copies imply the lower bound `11/16` for any rational marginal. -/
theorem chargeTangent (n x : Int) (hn : 0 ≤ n) (hx : x ≤ n) :
    0 ≤ 32 * (3*n*x*x - x*x*x) - 42*n*n*x + 5*n*n*n := by
  have h := Int.mul_nonneg (squareNonneg (4*x-n)) (show 0 ≤ 5*n-2*x by omega)
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at h ⊢
  simp only [← Int.mul_assoc] at h ⊢
  omega

/-- The expected charge of any three independent samples from the same
    four-symbol marginal is at least `11/16`, in rational frequencies. -/
theorem marginalCharge (n a b c d : Int)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : a + b + c + d = n) :
    11*n*n*n ≤ 16*((3*n*a*a-a*a*a) + (3*n*b*b-b*b*b) +
                    (3*n*c*c-c*c*c) + (3*n*d*d-d*d*d)) := by
  have hn : 0 ≤ n := by omega
  have h₁ := chargeTangent n a hn (by omega)
  have h₂ := chargeTangent n b hn (by omega)
  have h₃ := chargeTangent n c hn (by omega)
  have h₄ := chargeTangent n d hn (by omega)
  have hs := congrArg (fun e => n*n*e) ht
  simp only [Int.mul_add] at hs
  simp only [Int.mul_sub, Int.mul_add, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm] at *
  simp only [← Int.mul_assoc] at *
  omega

end TetrahedronTripleDifferences
