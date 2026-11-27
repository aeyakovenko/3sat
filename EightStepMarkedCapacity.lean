import Std

namespace EightStepMarkedCapacity

/-- The integer at an accepting terminal counts the selected target files there. -/
inductive Tree where
  | yes (targets : Nat)
  | no
  | branch (left right : Tree)

def targets : Tree → Nat
  | .yes n => n
  | .no => 0
  | .branch left right => targets left + targets right

def mark : Tree → Prop
  | .yes _ => False
  | .no => True
  | .branch left right => mark left ∨ mark right

/-- After the target comparison deadline, any residual subtree contains no targets. -/
def allowed : List Nat → Tree → Prop
  | [], t => targets t = 0
  | w :: _, .yes n => n ≤ w
  | _ :: _, .no => True
  | _ :: ws, .branch left right => allowed ws left ∧ allowed ws right

/-- Upper bounds for an arbitrary subtree and one containing a marked rejection. -/
def bound : List Nat → Nat × Nat
  | [] => (0, 0)
  | w :: ws =>
    let (f, e) := bound ws
    (max w (2*f), f+e)

theorem bounded (weights : List Nat) (t : Tree) (ok : allowed weights t) :
    targets t ≤ (bound weights).1 ∧ (mark t → targets t ≤ (bound weights).2) := by
  induction weights generalizing t with
  | nil =>
    have zero : targets t = 0 := ok
    simp [zero, bound]
  | cons w ws ih =>
    generalize hb : bound ws = bounds at *
    cases bounds with
    | mk f e =>
      cases t with
      | no => simp [targets, mark, bound, hb]
      | yes n =>
        have hn : n ≤ w := ok
        exact ⟨by simpa [targets,bound,hb] using (Nat.le_trans hn (Nat.le_max_left w (2*f))),
          False.elim⟩
      | branch l r =>
        obtain ⟨hl,hr⟩ := ok
        obtain ⟨lf,lm⟩ := ih l hl
        obtain ⟨rf,rm⟩ := ih r hr
        simp only [targets,mark,bound,hb]
        constructor
        · exact Nat.le_trans (by omega) (Nat.le_max_right w (2*f))
        · rintro (left | right)
          · have h := lm left
            omega
          · have h := rm right
            omega

theorem at_most_sixty_three (t : Tree) (ok : allowed [0,36,18,8,1] t)
    (negative : mark t) : targets t ≤ 63 :=
  (bounded _ t ok).2 negative

end EightStepMarkedCapacity
