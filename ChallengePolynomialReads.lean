import Std

namespace ChallengePolynomialReads

/-- Coefficients are stored in increasing order of degree. -/
def eval (point : Int) : List Int → Int
  | [] => 0
  | c :: cs => c + point * eval point cs

/-- Coefficients of (Z - root) times the input, with a carried low coefficient. -/
def linearCoeffs (root prev : Int) : List Int → List Int
  | [] => [prev]
  | c :: cs => (prev - root * c) :: linearCoeffs root c cs

theorem eval_linear (point root prev : Int) (cs : List Int) :
    eval point (linearCoeffs root prev cs) = prev + (point - root) * eval point cs := by
  induction cs generalizing prev with
  | nil => simp [eval, linearCoeffs]
  | cons c cs ih =>
    simp only [eval, linearCoeffs, ih, Int.mul_add, Int.sub_mul, Int.mul_sub,
      Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
    omega

def insertRoots : List Int → List Int → List Int
  | [], cs => cs
  | p :: ps, cs => insertRoots ps (linearCoeffs p 0 cs)

def product : List Int → Int
  | [] => 1
  | x :: xs => x * product xs

theorem eval_roots (point : Int) (ps cs : List Int) :
    eval point (insertRoots ps cs) =
    product (ps.map (fun p => point - p)) * eval point cs := by
  induction ps generalizing cs with
  | nil => simp [product, insertRoots]
  | cons p ps ih =>
    simp [product, insertRoots, ih, eval_linear, Int.mul_left_comm, Int.mul_comm, Int.mul_assoc]

/-- The same coefficient formula binds all simultaneous evaluation challenges. -/
theorem all_challenges_vanish (point : Int) (ps cs : List Int) (h : point ∈ ps) :
    eval point (insertRoots ps cs) = 0 := by
  rw [eval_roots]
  have hz : (0 : Int) ∈ ps.map (fun p => point - p) :=
    List.mem_map.mpr ⟨point, h, Int.sub_self point⟩
  have prod_zero (xs : List Int) : (0 : Int) ∈ xs → product xs = 0 := by
    induction xs with
    | nil => simp
    | cons x tail ih =>
      intro hit
      rcases List.mem_cons.mp hit with e | m
      · simp [product, ← e]
      · simp [product, ih m]
  simp [prod_zero _ hz]

end ChallengePolynomialReads
