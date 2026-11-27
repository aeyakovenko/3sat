import Std

namespace LiveValueReplay

/-- Integer units and upward rational rounding for the clock certificate. -/
def scale : Nat := 1000000000
def c : Nat := 1362200000
def ceilDiv (p q : Nat) : Nat := (p + q - 1) / q

def verifyStage (inner public : Nat) : Nat → Nat → Option Nat
  | 0, outer => some outer
  | steps + 1, outer => do
    let denominator := public * scale + inner * outer
    let updated := ceilDiv (c * public * inner * outer) (scale * denominator)
    guard (scale ≤ outer && outer ≤ inner && inner ≤ public)
    guard (100 * public * c < 97 * denominator)
    guard (updated < outer)
    verifyStage inner public steps updated

def verifyStages : List Nat → Nat → Nat → Option (Nat × Nat)
  | [], work, public => some (work, public)
  | count :: more, inner, lastPublic => do
    let public := ceilDiv (inner * lastPublic) scale
    let work ← verifyStage inner public count inner
    verifyStages more work public

/-- Checks all 103 applications with integer arithmetic, including the horizon
guard and the condition allowing a fixed public exponent within each stage. -/
theorem checked_clock_certificate :
    verifyStages [20, 25, 27, 30, 1] c c = some (992574225, 2508263363) := by
  decide

/-- The signed checker flips the prescribed verdict exactly on a passing chart. -/
theorem signed_verdict (desired chart actual : Bool)
    (equation : actual = if desired then !chart else chart)
    (sound : chart = true → actual = desired) :
    actual = desired ∧ chart = false := by
  cases desired <;> cases chart <;> simp_all

inductive Tree (Addr : Type) where
  | answer (v : Bool)
  | query (a : Addr) (low high : Tree Addr)

def Tree.eval (input : Addr → Bool) : Tree Addr → Bool
  | .answer v => v
  | .query a low high => if input a then high.eval input else low.eval input

def Tree.reads (input : Addr → Bool) : Tree Addr → List Addr
  | .answer _ => []
  | .query a low high => a :: (if input a then high.reads input else low.reads input)

theorem same_answers {Addr : Type} (tree : Tree Addr) (left right : Addr → Bool)
    (agree : ∀ a ∈ tree.reads left, left a = right a) :
    tree.eval left = tree.eval right := by
  induction tree with
  | answer => rfl
  | query a low high ihl ihh =>
    have h := agree a (by simp [Tree.reads])
    cases hl : left a with
    | false =>
      have hr : right a = false := h.symm.trans hl
      simp only [Tree.eval, hl, hr, Bool.false_eq_true, ↓reduceIte]
      exact ihl (fun v hv => agree v (by simp [Tree.reads, hl, hv]))
    | true =>
      have hr : right a = true := h.symm.trans hl
      simp only [Tree.eval, hl, hr, ↓reduceIte]
      exact ihh (fun v hv => agree v (by simp [Tree.reads, hl, hv]))

theorem sensitive_pin_is_read {Addr : Type} (tree : Tree Addr) (pin : Addr)
    (left right : Addr → Bool) (offPin : ∀ a, a ≠ pin → left a = right a)
    (changed : tree.eval left ≠ tree.eval right) :
    pin ∈ tree.reads left := by
  apply Classical.byContradiction
  intro absent
  apply changed
  apply same_answers
  intro a ha
  exact offPin _ (fun h => absent (h ▸ ha))

/-- After fixing the public certificate, every pivotal bit is inspected on
    some challenge for any choice of accepting private replies. -/
theorem alternating_challenges_cover_pin {Addr Challenge Reply : Type}
    (test : Challenge → Reply → Tree Addr) (chosen : Challenge → Reply)
    (left right : Addr → Bool) (pin : Addr)
    (offPin : ∀ a, a ≠ pin → left a = right a)
    (accepts : ∀ u, (test u (chosen u)).eval left = true)
    (rejects : ¬ ∀ u, ∃ v, (test u v).eval right = true) :
    ∃ u, pin ∈ (test u (chosen u)).reads left := by
  classical
  apply Classical.byContradiction
  intro uncovered
  apply rejects
  intro u
  refine ⟨chosen u, ?_⟩
  by_cases same : (test u (chosen u)).eval left = (test u (chosen u)).eval right
  · exact same.symm.trans (accepts u)
  · exact False.elim (uncovered ⟨u, sensitive_pin_is_read _ _ _ _ offPin same⟩)

end LiveValueReplay
