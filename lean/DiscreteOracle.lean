import Std

namespace DiscreteOracle

/-- A single test costs one. Its field interpretation is equality of already
    computed values. Only the discrete control of the tree is modeled here. -/
inductive Tree (σ : Type) where
  | leaf (answer : Bool)
  | test (read : σ → Bool) (yes no : Tree σ)

def Tree.run (x : σ) : Tree σ → Bool
  | .leaf answer => answer
  | .test read yes no => if read x then yes.run x else no.run x

def Tree.depth : Tree σ → Nat
  | .leaf _ => 0
  | .test _ yes no => 1 + max yes.depth no.depth

/-- The continuation is allowed to be noncomputable. A finite query has a
    finite table, regardless of which Boolean language supplied its answers. -/
def dispatch (bits : List (σ → Bool)) (next : List Bool → Tree σ) : Tree σ :=
  match bits with
  | [] => next []
  | r :: rs => .test r (dispatch rs (fun tail => next (true :: tail)))
                       (dispatch rs (fun tail => next (false :: tail)))

theorem dispatch_run (bits : List (σ → Bool)) (next : List Bool → Tree σ) (x : σ) :
    (dispatch bits next).run x = (next (bits.map (fun r => r x))).run x := by
  induction bits generalizing next with
  | nil => rfl
  | cons r rs ih =>
    cases hr : r x <;> simp [dispatch, Tree.run, hr, ih]

theorem dispatch_depth (bits : List (σ → Bool)) (next : List Bool → Tree σ) (h : Nat)
    (bounded : ∀ word, word.length = bits.length → (next word).depth ≤ h) :
    (dispatch bits next).depth ≤ bits.length + h := by
  induction bits generalizing next with
  | nil => simpa [dispatch] using bounded [] rfl
  | cons r rs ih =>
    have yes := ih (fun tail => next (true :: tail))
      (fun w len => bounded (true :: w) (by simp [len]))
    have no := ih (fun tail => next (false :: tail))
      (fun w len => bounded (false :: w) (by simp [len]))
    simp only [dispatch, Tree.depth, List.length_cons]
    omega

/-- read holds explicit query bits at an oracle node. -/
inductive WithOracle (σ : Type) where
  | leaf (answer : Bool)
  | test (read : σ → Bool) (yes no : WithOracle σ)
  | ask (read : List (σ → Bool)) (yes no : WithOracle σ)

def WithOracle.run (oracle : List Bool → Bool) (x : σ) : WithOracle σ → Bool
  | .leaf answer => answer
  | .test read yes no => if read x then yes.run oracle x else no.run oracle x
  | .ask read yes no =>
    if oracle (read.map (fun r => r x)) then yes.run oracle x else no.run oracle x

def WithOracle.cost : WithOracle σ → Nat
  | .leaf _ => 0
  | .test _ yes no => 1 + max yes.cost no.cost
  | .ask read yes no => read.length + max yes.cost no.cost

def WithOracle.compile (oracle : List Bool → Bool) : WithOracle σ → Tree σ
  | .leaf answer => .leaf answer
  | .test read yes no => .test read (yes.compile oracle) (no.compile oracle)
  | .ask read yes no =>
    let onYes := yes.compile oracle
    let onNo := no.compile oracle
    dispatch read (fun word => if oracle word then onYes else onNo)

theorem preserve (t : WithOracle σ) (oracle : List Bool → Bool) (x : σ) :
    (t.compile oracle).run x = t.run oracle x := by
  induction t with
  | leaf => rfl
  | test r _ _ iy ino => simp [WithOracle.compile, Tree.run, WithOracle.run, iy, ino]
  | ask rs _ _ iy ino =>
    simp only [WithOracle.compile, dispatch_run, WithOracle.run]
    split <;> assumption

theorem cost_bound (t : WithOracle σ) (oracle : List Bool → Bool) :
    (t.compile oracle).depth ≤ t.cost := by
  induction t with
  | leaf => exact Nat.le_refl _
  | test r _ _ iy ino =>
    simp only [WithOracle.compile, Tree.depth, WithOracle.cost]
    omega
  | ask rs _ _ iy ino =>
    simp only [WithOracle.compile, WithOracle.cost]
    apply dispatch_depth
    intro word _
    split <;> omega

end DiscreteOracle
