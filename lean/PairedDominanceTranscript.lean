import Std

namespace PairedDominanceTranscript

structure WeightedPoint where
  past : Bool
  left : Bool
  below : Bool
  weight : Int

def select (ok : Bool) (w : Int) : Int := if ok then w else 0

def lower (p : WeightedPoint) := select (p.past && p.left && p.below) p.weight

def upper (p : WeightedPoint) := select (!p.past && !p.left && !p.below) p.weight

def marginals (p : WeightedPoint) :=
  p.weight - select p.past p.weight - select p.left p.weight - select p.below p.weight
    + select (p.past && p.left) p.weight + select (p.past && p.below) p.weight
    + select (p.left && p.below) p.weight

theorem point_identity (p : WeightedPoint) : lower p + upper p = marginals p := by
  obtain ⟨a, b, c, w⟩ := p
  cases a <;> cases b <;> cases c <;> simp [lower, upper, marginals, select] <;> omega

def total (f : WeightedPoint → Int) : List WeightedPoint → Int
  | [] => 0
  | p :: rest => f p + total f rest

theorem projected_sum (ps : List WeightedPoint) :
    total lower ps + total upper ps = total marginals ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    simp only [total]
    have one := point_identity p
    omega

theorem truthful_reverse (ps : List WeightedPoint) (claim : Int) :
    claim + total upper ps = total marginals ps ↔ claim = total lower ps := by
  have both := projected_sum ps
  omega

def originalErrors : List (Int × List WeightedPoint) → Nat
  | [] => 0
  | (claim, ps) :: rest => (if claim = total lower ps then 0 else 1) + originalErrors rest

def pairedErrors : List (Int × List WeightedPoint) → Nat
  | [] => 0
  | (claim, ps) :: rest =>
    (if claim + total upper ps = total marginals ps then 0 else 1) + pairedErrors rest

theorem errors_preserved (qs : List (Int × List WeightedPoint)) :
    pairedErrors qs = originalErrors qs := by
  induction qs with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨claim, ps⟩ := q
    simp [pairedErrors, originalErrors, truthful_reverse, ih]

end PairedDominanceTranscript
