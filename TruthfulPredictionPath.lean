import Std

/-! Adaptive corrections along an entirely truthful execution. The state may
include the input, pending requests, previous emitted answers, memory and any
fixed random tape. `work` is arbitrary; recording it exposes the exact workload
on the successful path. -/
namespace TruthfulPredictionPath

structure Machine (S A W : Type) where
  prediction : S → A
  truth : S → A
  advance : S → A → S
  work : S → A → W

abbrev Record (S A W : Type) := S × A × W

variable {S A W : Type} (m : Machine S A W)

def run (s : S) : List (Option A) → List (Record S A W)
  | [] => []
  | c :: cs =>
    let a := c.getD (m.prediction s)
    (s,a,m.work s a) :: run (m.advance s a) cs

def truthful (s : S) : Nat → List (Record S A W)
  | 0 => []
  | n+1 =>
    let a := m.truth s
    (s,a,m.work s a) :: truthful (m.advance s a) n

def allCorrect (s : S) : List (Option A) → Prop
  | [] => True
  | c :: cs =>
    c.getD (m.prediction s) = m.truth s ∧ allCorrect (m.advance s (m.truth s)) cs

/-- The entire state/answer/work sequence agrees exactly, with the state of
an attempted run driven by its own emissions. -/
theorem run_eq_truthful (s : S) (plan : List (Option A)) :
    run m s plan = truthful m s plan.length ↔ allCorrect m s plan := by
  induction plan generalizing s with
  | nil => simp [run,truthful,allCorrect]
  | cons c cs ih =>
    simp only [run,truthful,List.length_cons,allCorrect,List.cons.injEq]
    constructor
    · rintro ⟨head,tail⟩
      have eq := congrArg (fun r : Record S A W => r.2.1) head
      change c.getD (m.prediction s) = m.truth s at eq
      rw [eq] at tail
      exact ⟨eq,(ih _).mp tail⟩
    · rintro ⟨eq,good⟩
      rw [eq]
      exact ⟨rfl,(ih _).mpr good⟩

variable [DecidableEq A]

def canonical (s : S) : Nat → List (Option A)
  | 0 => []
  | n+1 =>
    let a := m.truth s
    (if m.prediction s = a then none else some a) :: canonical (m.advance s a) n

def mistakes (s : S) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let a := m.truth s
    mistakes (m.advance s a) n + if m.prediction s = a then 0 else 1

theorem canonical_length (s : S) (n : Nat) : (canonical m s n).length = n := by
  induction n generalizing s <;> simp_all [canonical]

theorem canonical_cost (s : S) (n : Nat) :
    (canonical m s n).countP Option.isSome = mistakes m s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases same : m.prediction s = m.truth s <;> simp [canonical,mistakes,same,ih]

theorem canonical_exact (s : S) (n : Nat) : run m s (canonical m s n) = truthful m s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases same : m.prediction s = m.truth s <;> simp [canonical,run,truthful,same,ih]

/-- If an intervention must change the current prediction, then the successful
schedule is unique, even if subsequent requests and predictions look at it. -/
def realChanges (s : S) : List (Option A) → Prop
  | [] => True
  | c :: cs =>
    (∀ a, c = some a → a ≠ m.prediction s) ∧
      realChanges (m.advance s (c.getD (m.prediction s))) cs

theorem only_canonical (s : S) (plan : List (Option A)) (ok : allCorrect m s plan)
    (changes : realChanges m s plan) : plan = canonical m s plan.length := by
  induction plan generalizing s with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨agrees,rest⟩ := ok
    obtain ⟨real,restChanges⟩ := changes
    rw [agrees] at restChanges
    have tail := ih (m.advance s (m.truth s)) rest restChanges
    cases c with
    | none =>
      change m.prediction s = m.truth s at agrees
      simp only [List.length_cons,canonical,if_pos agrees]
      exact congrArg (List.cons _) tail
    | some a =>
      have diff := real a rfl
      change a = m.truth s at agrees
      subst a
      have ne := Ne.symm diff
      simp only [List.length_cons,canonical,if_neg ne]
      exact congrArg (List.cons _) tail

end TruthfulPredictionPath
