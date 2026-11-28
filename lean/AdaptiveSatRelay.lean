import Std

namespace AdaptiveSatRelay

inductive Plan (Q : Type) where
  | done (answer : Bool)
  | ask (question : Q) (onFalse onTrue : Plan Q)

def eval (bits : Q → Bool) : Plan Q → Bool
  | .done answer => answer
  | .ask q no yes => if bits q then eval bits yes else eval bits no

def visited (bits : Q → Bool) : Plan Q → List Q
  | .done _ => []
  | .ask q no yes => q :: (if bits q then visited bits yes else visited bits no)

theorem replay (p : Plan Q) (first second : Q → Bool)
    (agree : ∀ q ∈ visited first p, second q = first q) :
    eval second p = eval first p := by
  induction p with
  | done answer => rfl
  | ask q no yes ih₀ ih₁ =>
    have same : second q = first q := agree q (by simp [visited])
    cases h : first q with
    | false =>
      simp [eval, h, same]
      apply ih₀
      intro j hj
      exact agree j (by simp [visited, h, hj])
    | true =>
      simp [eval, h, same]
      apply ih₁
      intro j hj
      exact agree j (by simp [visited, h, hj])

def depth : Plan Q → Nat
  | .done _ => 0
  | .ask _ no yes => max (depth no) (depth yes) + 1

theorem short_walk (p : Plan Q) (bits : Q → Bool) :
    (visited bits p).length ≤ depth p := by
  induction p with
  | done => simp [visited, depth]
  | ask q no yes f t =>
    cases h : bits q with
    | false =>
      simp [visited, depth, h]
      exact Nat.le_trans f (Nat.le_max_left _ _)
    | true =>
      simp [visited, depth, h]
      exact Nat.le_trans t (Nat.le_max_right _ _)

/-- Compute a gate tree using only the questions chosen by its local plans. -/
def treeValue (root : Site) (child : Site → Q → Site) (plans : Site → Plan Q)
    (leaf : Site → Bool) : Nat → Bool
  | 0 => leaf root
  | levels+1 =>
    eval (fun q => treeValue (child root q) child plans leaf levels) (plans root)

theorem faithful (answer : Site → Bool) (child : Site → Q → Site)
    (plans : Site → Plan Q) (leaf : Site → Bool)
    (base : ∀ x, leaf x = answer x)
    (step : ∀ x, eval (fun q => answer (child x q)) (plans x) = answer x)
    (x : Site) (d : Nat) : treeValue x child plans leaf d = answer x := by
  induction d generalizing x with
  | zero => exact base x
  | succ d ih =>
    change eval (fun q => treeValue (child x q) child plans leaf d) (plans x) = answer x
    rw [← step x]
    apply replay
    intro j _
    exact ih (child x j)

end AdaptiveSatRelay
