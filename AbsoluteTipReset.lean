import Std

/-! Count every absolute incoming and outgoing boundary, with the previous
tip and current base separately specified. The order within the tile is fixed. -/
namespace AbsoluteTipReset

abbrev State := Fin 9

def prevTip (s : State) := s.val / 3
def base (s : State) := s.val % 3
def isD (s : State) := prevTip s != base s

def delta (mask i : Nat) := if mask.testBit i then 2 else 1

/-- Add the signed base increments; the unique triangle tip is the other color. -/
def trace (n mask y : Nat) : List Nat × Nat :=
  match n with
  | 0 => ([],y)
  | k+1 =>
    let d := delta mask 0
    let tail := trace k (mask/2) ((y+d)%3)
    (((y+3-d)%3)::tail.1,tail.2)

def reset := [1,2,0,5,3,6,4]

/-- Count sign strings compatible with both specified absolute states,
including the inequality between the incoming previous tip and the first visit. -/
def transfer (order : List Nat) (s t : State) : Nat :=
  ((List.range (2^order.length)).filter fun mask =>
    let (tips,lastBase) := trace order.length mask (base s)
    let visits := order.map fun i => tips[i]!
    let lane := prevTip s :: visits
    (lane.zip lane.tail).all (fun (a,b) => a != b) &&
      visits.getLast! == prevTip t && lastBase == base t).length

/-- The actual 9×9 matrix has identical rows, with precisely two extensions
to each of the six different-color states. -/
theorem absolute_reset : ∀ s t : State,
    transfer reset s t = if isD t then 2 else 0 := by decide

/-- A matrix element of U K U, written as a sum over the six D states and
all possible intermediate exit states. `weight` can be any suffix count. -/
def total (K : State → State → Nat) (s : State) :=
  ((List.finRange 9).map (K s)).sum

def sandwiched (K : State → State → Nat) (s t : State) :=
  ((List.finRange 9).map fun u => transfer reset s u *
    ((List.finRange 9).map fun v => K u v * transfer reset v t).sum).sum

private theorem sum_mul_right (xs : List State) (f : State → Nat) (w : Nat) :
    (xs.map (fun x => f x * w)).sum = (xs.map f).sum * w := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul]

theorem sandwich_multiplier (K : State → State → Nat) (w : Nat)
    (known : ∀ u, isD u = true → total K u = w) (s t : State) :
    sandwiched K s t = if isD t then 24*w else 0 := by
  simp only [sandwiched, absolute_reset, sum_mul_right]
  change ((List.finRange 9).map fun u =>
    (if isD u then 2 else 0)*(total K u*(if isD t then 2 else 0))).sum = _
  have simplify (u : State) :
      (if isD u then 2 else 0)*(total K u*(if isD t then 2 else 0)) =
      if isD u then 2*(w*(if isD t then 2 else 0)) else 0 := by
    cases h : isD u <;> simp [h,known]
  simp only [simplify]
  have expand (v : Nat) : ((List.finRange 9).map (fun u => if isD u then v else 0)).sum = 6*v := by
    change 0+(v+(v+(v+(0+(v+(v+(v+(0+0)))))))) = _
    omega
  rw [expand]
  cases h : isD t <;> simp [h] <;> omega

end AbsoluteTipReset
