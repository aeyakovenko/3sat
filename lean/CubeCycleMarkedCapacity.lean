import Std

/-!
Cube-cycle catalog: marked-tree capacity recurrence for the cube-cycle catalog.

The recurrence and its proof are those of `EightStepMarkedCapacity.lean` in the
journal (model proof of the nine-step theorem); only the weights are new.
A program in which every input halts within eight instructions unfolds into a
binary tree of comparisons.  A REJECT leaf reached after `d` comparisons holds
at most `w_d` covers (the leaf capacities computed by `cube_cycle_leaf_capacity`, and
for stores the bound of clock-bounds-for-the-four-word-cube-cycle-catalog.md section 3.5), a leaf after more than four
comparisons holds none, and at least one leaf is an ACCEPT leaf.
-/

namespace CubeCycleMarkedCapacity

/-- The integer at a rejecting terminal counts the covers that reach it. -/
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

/-- `allowed ws t`: a leaf at comparison depth `d` holds at most `ws[d]` targets,
    and below the listed depths no targets remain. -/
def allowed : List Nat → Tree → Prop
  | [], t => targets t = 0
  | w :: _, .yes n => n ≤ w
  | _ :: _, .no => True
  | _ :: ws, .branch left right => allowed ws left ∧ allowed ws right

/-- Capacity of an arbitrary subtree and of one that contains an accepting leaf. -/
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

/-- Eight-step deadline, leaf capacities 225, 147, 81, 81 after 1, 2, 3, 4 comparisons:
    a correct tree certifies at most 1215 of the 2207 covers. -/
theorem eight_steps (t : Tree) (ok : allowed [0,225,147,81,81] t)
    (accepting : mark t) : targets t ≤ 1215 :=
  (bounded _ t ok).2 accepting

/-- Class (F) with stores: a leaf whose last STORE is never read back on a cover splits into
    at most four leaves of a path with one more comparison (clock-bounds-for-the-four-word-cube-cycle-catalog.md, section 3.5), which
    gives the weights 1296 = 4 * 324 and 324 = 4 * 81 after one and two comparisons. -/
theorem eight_steps_class_F (t : Tree) (ok : allowed [0,1296,324,81,81] t)
    (accepting : mark t) : targets t ≤ 1863 :=
  (bounded _ t ok).2 accepting

/-- Seven-step deadline: no rejecting leaf holds a cover at all. -/
theorem seven_steps (t : Tree) (ok : allowed [0,0,0,0] t) : targets t ≤ 0 :=
  (bounded _ t ok).1

/-- Margins: with the two deepest weights fixed at 81, the first two may grow to 1639 and 324. -/
theorem margin_shallow (t : Tree) (ok : allowed [0,1639,324,81,81] t)
    (accepting : mark t) : targets t ≤ 2206 :=
  (bounded _ t ok).2 accepting

/-- Margins: any weights below 1176, 588, 294, 147 would do. -/
theorem margin_uniform (t : Tree) (ok : allowed [0,1176,588,294,147] t)
    (accepting : mark t) : targets t ≤ 2205 :=
  (bounded _ t ok).2 accepting

theorem below_all_covers : 1215 < 2207 ∧ 1863 < 2207 ∧ 2206 < 2207 ∧ 2205 < 2207 := by decide

end CubeCycleMarkedCapacity
