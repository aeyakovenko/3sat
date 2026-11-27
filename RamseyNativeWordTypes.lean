import Std

namespace RamseyNativeWordTypes

/-- A producer cone in a component whose undirected incidence graph is a tree. -/
inductive Expr (Op Src : Type) where
  | source (v : Src)
  | gate (op : Op) (left right : Expr Op Src)

def Expr.size : Expr Op Src → Nat
  | .source _ => 0
  | .gate _ u v => u.size + v.size + 1

def Expr.forget : Expr Op Src → Expr Op Unit
  | .source _ => .source ()
  | .gate f u v => .gate f u.forget v.forget

def Expr.eval (alu : Op → W → W → W) (src : Src → W) : Expr Op Src → W
  | .source v => src v
  | .gate f u v => alu f (u.eval alu src) (v.eval alu src)

theorem Expr.size_forget (e : Expr Op Src) : e.forget.size = e.size := by
  induction e with
  | source => rfl
  | gate _ u v hu hv => simp [Expr.size, Expr.forget, hu, hv]

theorem Expr.eval_forget (e : Expr Op Src) (alu : Op → W → W → W) (a : W) :
    e.eval alu (fun _ => a) = e.forget.eval alu (fun _ => a) := by
  induction e with
  | source => rfl
  | gate _ u v hu hv => simp [Expr.eval, Expr.forget, hu, hv]

structure Guard (Op Src Test : Type) where
  left : Expr Op Src
  right : Expr Op Src
  kind : Test

def Guard.outcome (g : Guard Op Src Test) (alu : Op → W → W → W)
    (check : Test → W → W → Bool) (a : W) : Bool :=
  check g.kind (g.left.eval alu (fun _ => a)) (g.right.eval alu (fun _ => a))

/-- The two source words induce the same ordered guard table on all small unary terms. -/
def SameType (s : Nat) (alu : Op → W → W → W) (check : Test → W → W → Bool)
    (a b : W) : Prop :=
  ∀ (u v : Expr Op Unit), u.size ≤ s → v.size ≤ s → ∀ t,
    check t (u.eval alu (fun _ => a)) (v.eval alu (fun _ => a)) =
    check t (u.eval alu (fun _ => b)) (v.eval alu (fun _ => b))

theorem guard_indistinguishable (alu : Op → W → W → W) (check : Test → W → W → Bool)
    (same : SameType s alu check a b) (g : Guard Op Src Test)
    (left : g.left.size ≤ s) (right : g.right.size ≤ s) :
    g.outcome alu check a = g.outcome alu check b := by
  unfold Guard.outcome
  rw [g.left.eval_forget alu a, g.left.eval_forget alu b,
      g.right.eval_forget alu a, g.right.eval_forget alu b]
  exact same g.left.forget g.right.forget (by simpa [Expr.size_forget] using left)
    (by simpa [Expr.size_forget] using right) g.kind

theorem all_guard_outcomes (alu : Op → W → W → W) (check : Test → W → W → Bool)
    (same : SameType s alu check a b) (gs : List (Guard Op Src Test))
    (small : ∀ g ∈ gs, g.left.size ≤ s ∧ g.right.size ≤ s) :
    gs.map (fun g => g.outcome alu check a) = gs.map (fun g => g.outcome alu check b) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have h := small g (by simp)
    have tail := ih (fun f member => small f (by simp [member]))
    simp only [List.map_cons, guard_indistinguishable alu check same g h.1 h.2, tail]

end RamseyNativeWordTypes
