import Std

namespace AdaptiveChecksumQueries

def sign : Bool → Int
  | false => 1
  | true => -1

def subsetProducts : List Int → List Int
  | [] => [1]
  | x :: xs =>
    let previous := subsetProducts xs
    previous ++ previous.map (fun y => x * y)

private theorem scaledSum (x : Int) (terms : List Int) :
    (terms.map (fun y => x * y)).sum = x * terms.sum := by
  induction terms with
  | nil => simp
  | cons a as ih => simp [ih, Int.mul_add]

private theorem appendSum (a b : List Int) :
    (a ++ b).sum = a.sum + b.sum := by
  induction a with
  | nil => simp
  | cons x xs ih => simp [ih, Int.add_assoc]

def product : List Int → Int
  | [] => 1
  | x :: xs => x * product xs

/-- The path indicator after clearing its power-of-two denominator. -/
theorem pathExpansion (terms : List Int) :
    (subsetProducts terms).sum = product (terms.map (fun x => 1 + x)) := by
  induction terms with
  | nil => simp [subsetProducts, product]
  | cons x xs ih =>
    simp [subsetProducts, product, appendSum, scaledSum, ih, Int.add_mul]

inductive Tree (Q : Type) : Nat → Type where
  | leaf (bit : Bool) : Tree Q 0
  | node {n : Nat} (query : Q) (left right : Tree Q n) : Tree Q (n + 1)

def eval {Q : Type} (answer : Q → Bool) : {n : Nat} → Tree Q n → Bool
  | _, .leaf bit => bit
  | _, .node q left right =>
    if answer q then eval answer right else eval answer left

def weightedLeaves {Q : Type} (answer : Q → Bool) : {n : Nat} → Tree Q n → Int
  | _, .leaf bit => sign bit
  | _, .node q left right =>
    (1 + sign (answer q)) * weightedLeaves answer left +
      (1 - sign (answer q)) * weightedLeaves answer right

/-- Summing all scaled signed leaf indicators gives the sign of the adaptive reply. -/
theorem evaluateLeafExpansion {Q : Type} (answer : Q → Bool) {n : Nat} (tree : Tree Q n) :
    weightedLeaves answer tree = (2 : Int)^n * sign (eval answer tree) := by
  induction tree with
  | leaf bit => simp [weightedLeaves, eval]
  | @node n q left right il ir =>
    cases b : answer q <;>
      simp [eval, weightedLeaves, b, sign, il, ir, Int.pow_succ,
        Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

def parity : List Bool → Bool
  | [] => false
  | b :: bs => b ^^ parity bs

private theorem switchXors : ∀ a b c d : Bool,
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide

/-- Old replies cancel when the parity on both tables uses the same selectors. -/
theorem relabelPath (path : List (Bool × Bool)) :
    parity (path.map (fun pair => pair.1 ^^ pair.2)) =
      (parity (path.map Prod.fst) ^^ parity (path.map Prod.snd)) := by
  induction path with
  | nil => rfl
  | cons pair path ih =>
    simp only [List.map_cons, parity, ih]
    apply switchXors

end AdaptiveChecksumQueries
