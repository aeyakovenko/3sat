import Std

namespace PinnedChartCylinders

inductive ReadTree (BitIndex State : Type)
  | done (state : State)
  | read (index : BitIndex) (zero one : ReadTree BitIndex State)

variable {BitIndex State Cut : Type}

def ReadTree.eval (x : BitIndex → Bool) : ReadTree BitIndex State → State
  | .done state => state
  | .read i zero one => if x i then one.eval x else zero.eval x

def ReadTree.path (x : BitIndex → Bool) : ReadTree BitIndex State → List BitIndex
  | .done _ => []
  | .read i zero one => i :: (if x i then one.path x else zero.path x)

def ReadTree.depth : ReadTree BitIndex State → Nat
  | .done _ => 0
  | .read _ zero one => 1 + max zero.depth one.depth

theorem ReadTree.path_length (tree : ReadTree BitIndex State) (x : BitIndex → Bool) :
    (tree.path x).length ≤ tree.depth := by
  induction tree with
  | done _ => simp [path, depth]
  | read i z o hz ho =>
    cases h : x i <;> simp [path, depth, h] <;> omega

theorem ReadTree.replay (tree : ReadTree BitIndex State) (x y : BitIndex → Bool)
    (agree : ∀ i ∈ tree.path x, y i = x i) : tree.eval y = tree.eval x := by
  induction tree with
  | done _ => rfl
  | read i z o hz ho =>
    have hi : y i = x i := agree i (by simp [path])
    cases h : x i with
    | false =>
      simp [eval, hi, h]
      apply hz
      intro j hj
      exact agree j (by simp [path, h, hj])
    | true =>
      simp [eval, hi, h]
      apply ho
      intro j hj
      exact agree j (by simp [path, h, hj])

/-- For each gap, its actual native block is represented by a tree with full
    start and end states. No bound is imposed on the state space. -/
structure Chart (BitIndex State Cut : Type) where
  entrance : Cut → State → Prop
  exitSet : Cut → State → Prop
  block : Cut → State → ReadTree BitIndex State

def Chart.passes (chart : Chart BitIndex State Cut) (x : BitIndex → Bool) : Prop :=
  ∀ c s, chart.entrance c s → chart.exitSet c ((chart.block c s).eval x)

theorem bad_gap_cylinder (chart : Chart BitIndex State Cut) (width : Nat)
    (bounded : ∀ c s, (chart.block c s).depth ≤ width)
    (x : BitIndex → Bool) (bad : ¬ chart.passes x) :
    ∃ coordinates : List BitIndex, coordinates.length ≤ width ∧
      ∀ y : BitIndex → Bool, (∀ i ∈ coordinates, y i = x i) → ¬ chart.passes y := by
  classical
  simp only [Chart.passes, Classical.not_forall, Classical.not_imp] at bad
  obtain ⟨c, s, entrance, failed⟩ := bad
  let tree := chart.block c s
  refine ⟨tree.path x, Nat.le_trans (tree.path_length x) (bounded c s), ?_⟩
  intro y agree passed
  have replay := tree.replay x y agree
  exact failed (replay ▸ passed c s entrance)

end PinnedChartCylinders
