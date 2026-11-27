import Std

/- A binary OR tree with two time-limited tests at each internal node. `none`
   means the test timed out. Node labels may include the interval and its state. -/
namespace DyadicHalfTimeout

inductive Tree (Leaf Node : Type) where
  | leaf (label : Leaf)
  | branch (label : Node) (left right : Tree Leaf Node)

def verdict (value : Leaf → Bool) : Tree Leaf Node → Bool
  | .leaf x => value x
  | .branch _ left right => verdict value left || verdict value right

abbrev Tests (Node : Type) := Node → Option Bool × Option Bool

abbrev TimelyIsSound (test : Option Bool) (value : Bool) : Prop :=
  test = none ∨ test = some value

/-- On the tree in question, timely results are sound, and two timeouts are
    ruled out whenever the children's verdicts differ. -/
def Sound (value : Leaf → Bool) (tests : Tests Node) : Tree Leaf Node → Prop
  | .leaf _ => True
  | .branch v left right =>
    TimelyIsSound (tests v).1 (verdict value left) ∧
    TimelyIsSound (tests v).2 (verdict value right) ∧
    ((tests v).1 = none → (tests v).2 = none → verdict value left = verdict value right) ∧
    Sound value tests left ∧ Sound value tests right

inductive Action where
  | halt (result : Bool)
  | visitLeft
  | visitRight

/-- The decoder reads both test outcomes, then follows at most one child. -/
def decideNode : Option Bool → Option Bool → Action
  | some true, _ | _, some true => .halt true
  | some false, some false => .halt false
  | some false, none => .visitRight
  | none, some false | none, none => .visitLeft

private def applyAction (left right : Bool) : Action → Bool
  | .halt a => a
  | .visitLeft => left
  | .visitRight => right

private theorem decideNode_correct (left right : Bool) (a b : Option Bool)
    (ha : TimelyIsSound a left) (hb : TimelyIsSound b right)
    (both : a = none → b = none → left = right) :
    applyAction left right (decideNode a b) = (left || right) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    cases left <;> cases right <;> simp_all [applyAction, decideNode]

def run (value : Leaf → Bool) (tests : Tests Node) : Tree Leaf Node → Bool
  | .leaf x => value x
  | .branch v left right =>
    match decideNode (tests v).1 (tests v).2 with
    | .halt a => a
    | .visitLeft => run value tests left
    | .visitRight => run value tests right

/-- Exact for arbitrary shaped finite trees, arbitrary leaf bits, and any tree
    on which the tests satisfy `Sound`. -/
theorem run_correct (value : Leaf → Bool) (tests : Tests Node) (t : Tree Leaf Node)
    (hs : Sound value tests t) : run value tests t = verdict value t := by
  induction t with
  | leaf _ => rfl
  | branch v left right ihl ihr =>
    obtain ⟨ha, hb, both, hl, hr⟩ := hs
    have step :=  decideNode_correct (verdict value left) (verdict value right) _ _ ha hb both
    cases h : decideNode (tests v).1 (tests v).2 <;>
      simpa [run, verdict, h, applyAction, ihl hl, ihr hr] using step

/-- Work incurred by the actual route. `testCost` includes the cost of both
    time-limited tests and `leafCost` may depend on the terminal leaf. -/
def work (leafCost : Leaf → Nat) (testCost : Node → Nat) (tests : Tests Node) :
    Tree Leaf Node → Nat
  | .leaf x => leafCost x
  | .branch v left right => testCost v +
    match decideNode (tests v).1 (tests v).2 with
    | .halt _ => 0
    | .visitLeft => work leafCost testCost tests left
    | .visitRight => work leafCost testCost tests right

def maxPathCost (leafCost : Leaf → Nat) (testCost : Node → Nat) : Tree Leaf Node → Nat
  | .leaf x => leafCost x
  | .branch v left right =>
    testCost v + max (maxPathCost leafCost testCost left) (maxPathCost leafCost testCost right)

/-- The accounting pays a single path, even when both tests time out. -/
theorem work_le_path_cost (leafCost : Leaf → Nat) (testCost : Node → Nat) (tests : Tests Node)
    (t : Tree Leaf Node) : work leafCost testCost tests t ≤ maxPathCost leafCost testCost t := by
  induction t with
  | leaf _ => exact Nat.le_refl _
  | branch v left right ihl ihr =>
    cases h : decideNode (tests v).1 (tests v).2 with
    | halt _ => simp [work, maxPathCost, h]
    | visitLeft =>
      simp only [work, maxPathCost, h]
      exact Nat.add_le_add_left (Nat.le_trans ihl (Nat.le_max_left _ _)) _
    | visitRight =>
      simp only [work, maxPathCost, h]
      exact Nat.add_le_add_left (Nat.le_trans ihr (Nat.le_max_right _ _)) _

#print axioms run_correct
#print axioms work_le_path_cost

end DyadicHalfTimeout
