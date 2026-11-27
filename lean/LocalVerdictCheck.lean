import Std

namespace LocalVerdictCheck

/-- A terminal has no children and a known result combine []. A binary
    restriction can use [left,right] with Boolean disjunction. -/
structure Rule (α : Type) where
  children : List α
  combine : List Bool → Bool

def LocalOK (rule : α → Rule α) (verdict : α → Bool) (x : α) : Prop :=
  verdict x = (rule x).combine ((rule x).children.map verdict)

/-- Every internal node of the path passes the local test. -/
inductive CheckedPath (rule : α → Rule α) (passes : α → Prop) : α → α → Nat → Prop where
  | stop (x : α) : CheckedPath rule passes x x 0
  | step {x y z : α} {n : Nat} (ok : passes x) (child : y ∈ (rule x).children)
      (tail : CheckedPath rule passes y z n) : CheckedPath rule passes x z (n+1)

private theorem wrongChild (rule : α → Rule α) (actual guess : α → Bool) (x : α)
    (correct : LocalOK rule actual x) (passes : LocalOK rule guess x)
    (wrong : guess x ≠ actual x) : ∃ y ∈ (rule x).children, guess y ≠ actual y := by
  apply Classical.byContradiction
  intro noneWrong
  have same : (rule x).children.map guess = (rule x).children.map actual := by
    apply List.map_congr_left
    intro y hy
    exact Classical.byContradiction (fun different => noneWrong ⟨y, hy, different⟩)
  exact wrong (passes.trans ((congrArg (rule x).combine same).trans correct.symm))

/-- A wrong initial verdict leads to a first failing local test, even if the
    candidate's other answers and the restriction DAG are chosen adversarially. -/
theorem findFailure (rule : α → Rule α) (actual guess : α → Bool)
    (rank : α → Nat) (decreases : ∀ x y, y ∈ (rule x).children → rank y < rank x)
    (correct : ∀ x, LocalOK rule actual x) (x : α) (wrong : guess x ≠ actual x) :
    ∃ z n, CheckedPath rule (LocalOK rule guess) x z n ∧
      ¬ LocalOK rule guess z ∧ guess z ≠ actual z := by
  by_cases passes : LocalOK rule guess x
  · obtain ⟨y,hy,bad⟩ := wrongChild rule actual guess x (correct x) passes wrong
    obtain ⟨z,n,path,fails,lastWrong⟩ := findFailure rule actual guess rank decreases correct y bad
    exact ⟨z,n+1,.step passes hy path,fails,lastWrong⟩
  · exact ⟨x,0,.stop x,passes,wrong⟩
termination_by rank x
decreasing_by exact decreases x y hy

theorem pathLengthBound (rule : α → Rule α) (passes : α → Prop) (rank : α → Nat)
    (decreases : ∀ x y, y ∈ (rule x).children → rank y < rank x)
    {x z n} (path : CheckedPath rule passes x z n) : n + rank z ≤ rank x := by
  induction path with
  | stop => simp
  | step ok edge tail ih => have := decreases _ _ edge; omega

theorem encodingBound (rule : α → Rule α) (passes : α → Prop) (size : α → Nat)
    (shrinks : ∀ x y, y ∈ (rule x).children → size y ≤ size x)
    {x z n} (path : CheckedPath rule passes x z n) : size z ≤ size x := by
  induction path with
  | stop => exact Nat.le_refl _
  | step ok edge tail ih => exact Nat.le_trans ih (shrinks _ _ edge)

/-- It suffices to check for local failure on reachable instances no larger
    than the incorrect original instance. -/
theorem boundedFailure (rule : α → Rule α) (actual guess : α → Bool) (rank size : α → Nat)
    (decreases : ∀ x y, y ∈ (rule x).children → rank y < rank x)
    (shrinks : ∀ x y, y ∈ (rule x).children → size y ≤ size x)
    (correct : ∀ x, LocalOK rule actual x) (x : α) (wrong : guess x ≠ actual x) :
    ∃ z n, CheckedPath rule (LocalOK rule guess) x z n ∧
      ¬ LocalOK rule guess z ∧ size z ≤ size x ∧ n + rank z ≤ rank x := by
  obtain ⟨z,n,path,fails,_⟩ := findFailure rule actual guess rank decreases correct x wrong
  exact ⟨z,n,path,fails,encodingBound rule _ size shrinks path,
    pathLengthBound rule _ rank decreases path⟩

end LocalVerdictCheck
