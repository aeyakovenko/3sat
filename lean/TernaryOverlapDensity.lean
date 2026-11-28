import Std

namespace TernaryOverlapDensity

/-- Hamming choices of five independent coins. When the two triples share two
    variables the fifth coin is unused. A return of 0 denotes rejection. -/
inductive Kind | one | two deriving DecidableEq, Repr

def charge (k : Kind) (bits : Nat) : Nat :=
  let b := bits.testBit
  match k with
  | .one =>
    if !b 0 then 1
    else if !(b 1 && b 2) && !(b 3 && b 4) then 2 else 0
  | .two =>
    if !(b 0 && b 1) then 1
    else if !b 2 && !b 3 then 2 else 0

def count (k : Kind) (d : Nat) :=
  ((List.range 32).filter (fun x => charge k x == d)).length

theorem branch_counts :
    (count .one 1,count .one 2,count .two 1,count .two 2) =
    (16,9,24,2) := by decide +kernel

/-- x and y bound the two classes of residual branches, measured against
    the same denominator. Adjoining one or two exposed zeroes gives their
    respective factors 8/7 and (8/7)^2. -/
theorem one_step (k : Kind) (x y z : Nat)
    (hx : 7*x ≤ 8*z) (hy : 49*y ≤ 64*z) :
    49*(count k 1*x+count k 2*y) ≤ 32*46*z := by
  cases k
  · have h : count .one 1 = 16 ∧ count .one 2 = 9 := by decide +kernel
    rw [h.1,h.2]
    omega
  · have h : count .two 1 = 24 ∧ count .two 2 = 2 := by decide +kernel
    rw [h.1,h.2]
    omega

/-- Counts on 32 coin positions with a factor 7^(2-d)8^d per successful
    leaf. The denominator for one normalized step is 32*49. -/
def normalizedNumerator (k : Kind) :=
  count k 1 * (7*8) + count k 2 * (8*8)

theorem exact_weight (k : Kind) : normalizedNumerator k = 32*46 := by
  cases k <;> decide +kernel

def combinedWeight : List Kind → Nat
  | [] => 1
  | k :: rest => normalizedNumerator k * combinedWeight rest

theorem product_weight (ks : List Kind) :
    combinedWeight ks = (32*46)^ks.length := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
    simp only [combinedWeight, List.length_cons,
      exact_weight, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

def gadget : List Nat := [7,11,28]

def independent (s : Nat) : Bool := gadget.all (fun e => s &&& e != e)

def hits (s : Nat) : Bool := gadget.all (fun e => s &&& e != 0)

def size (s : Nat) : Nat := ((List.range 5).filter s.testBit).length

theorem sharp_five_vertex_example :
    ((List.range 32).filter independent).length = 23 ∧
    ((List.range 32).filter (fun s => size s < 2 && hits s)).isEmpty ∧
    hits 5 ∧ size 5 = 2 ∧ 23*64*49 = 32*49*46 := by decide +kernel

end TernaryOverlapDensity
