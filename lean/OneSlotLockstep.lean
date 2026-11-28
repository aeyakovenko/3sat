import Std
namespace OneSlotLockstep

/-- The private numeric selector is used by a control test, never by memory or guest action. -/
def done (sel first second : Bool) : Bool :=
  (first && second) || (if sel then second && !first else first && !second)

theorem stop_iff (sel first second : Bool) :
    done sel first second = if sel then second else first := by
  cases sel <;> cases first <;> cases second <;> decide

def run {α : Type} (step : α → α) (s : α) : Nat → α
  | 0 => s
  | n+1 => step (run step s n)

theorem paired_state {α β : Type} (f : α → α) (g : β → β) (a : α) (b : β) (n : Nat) :
    run (fun p : α × β => (f p.1, g p.2)) (a,b) n = (run f a n, run g b n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run,ih]

theorem same_clock (sel : Bool) (first second : Nat) (i : Nat) :
    done sel (decide (first ≤ i)) (decide (second ≤ i)) =
      decide ((if sel then second else first) ≤ i) := by
  rw [stop_iff]
  cases sel <;> rfl

def unitG (u p q : Bool) : Bool :=
  (u || p || q) && (u || p || !q) && (u || !p || q) && (u || !p || !q)

def guarded (u x p : Bool) : Bool :=
  ((!u || x) || p) && ((!u || x) || !p)

theorem unit_models (u p q : Bool) : unitG u p q = u := by
  cases u <;> cases p <;> cases q <;> decide

theorem guarded_models (u x p : Bool) : guarded u x p = (!u || x) := by
  cases u <;> cases x <;> cases p <;> decide

/-- Early pruning only rejects a clause when every literal is assigned false. -/
def killed (a b c : Option Bool) : Bool :=
  a == some false && b == some false && c == some false

def lit (positive : Bool) (val : Option Bool) : Option Bool :=
  val.map (fun b => if positive then b else !b)

theorem no_early_unit (us ps qs : Bool) :
    killed (lit us none) (lit ps none) (lit qs none) = false := by rfl

theorem no_early_guarded (data : Option Bool) (ps : Bool) :
    killed (lit false none) data (lit ps none) = false := by rfl

/-- A selector can remove a live state only by retiring; it cannot change a continuing trajectory. -/
def live {α : Type} (step : α → α) (retire : α → Bool) (initial : α) : Nat → Option α
  | 0 => some initial
  | n+1 => (live step retire initial n).bind (fun s => if retire s then none else some (step s))

theorem live_agrees {α : Type} (step : α → α) (retire : α → Bool) (s a : α) (n : Nat)
    (h : live step retire s n = some a) : a = run step s n := by
  induction n generalizing a with
  | zero => simpa [live, run] using h.symm
  | succ n ih =>
    cases he : live step retire s n with
    | none => simp [live, he] at h
    | some t =>
      have ht := ih t he
      cases hs : retire t <;> simp [live, he, hs] at h
      simpa [run, ← ht] using h.symm

theorem common_live_prefix {α : Type} (step : α → α) (r t : α → Bool) (s a b : α) (n : Nat)
    (ha : live step r s n = some a) (hb : live step t s n = some b) : a = b :=
  (live_agrees step r s a n ha).trans (live_agrees step t s b n hb).symm

/-- On a pure data prefix the padded units are neither falsified nor already satisfied. -/
def witnessed (a b c : Option Bool) : Bool :=
  a == some true || b == some true || c == some true

theorem unit_not_already_true (us ps qs : Bool) :
    witnessed (lit us none) (lit ps none) (lit qs none) = false := by rfl

end OneSlotLockstep
