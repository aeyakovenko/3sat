import Std

namespace ShiftedStrideOrigin

variable {α : Type} [DecidableEq α]

def put (m : α → α) (address value : α) : α → α :=
  fun x => if x = address then value else m x

/-- The payload is the successor cursor in the real scan. Keeping it
    explicit lets the same statement cover any fixed stride and modulus. -/
def scan (m : α → α) (p next : α) : α → α := put m (m p) next

inductive Event (α : Type) where
  | normal (cursor next : α)
  | exception (address value : α)
  | skip

def perform (m : α → α) : Event α → (α → α)
  | .normal p q => scan m p q
  | .exception a v => put m a v
  | .skip => m

def run (m : α → α) (events : List (Event α)) : α → α :=
  events.foldl perform m

/-- The label B can occur as a memory value only at the anchor A;
    the anchor itself need not still contain it. -/
def confined (m : α → α) (A B : α) : Prop := ∀ x, x ≠ A → m x ≠ B

theorem confined_put {m : α → α} {A B dest v : α}
    (h : confined m A B) (fresh : v ≠ B) : confined (put m dest v) A B := by
  intro x hx
  by_cases hxd : x = dest
  · simpa [put, hxd] using fresh
  · simpa [put, hxd] using h x hx

/-- An early pair of high zero cells produces B at the zero cell, then
    overwrites it there on the very next step, with no other memory change. -/
theorem early_pair {m : α → α} {zero before B later : α}
    (prevZero : m before = zero) (atZero : m B = zero) (hne : B ≠ zero) :
    scan (scan m before B) B later = put m zero later := by
  funext x
  by_cases hx : x = zero <;> simp [scan, put, prevZero, atZero, hne, hx]

def safe (A B : α) : Event α → Prop
  | .normal p q => p ≠ A ∧ q ≠ B
  | .exception a v => a ≠ B ∧ v ≠ B
  | .skip => True

theorem survives_event {m : α → α} {A B i : α} (event : Event α)
    (ok : safe A B event) (onlyAt : confined m A B) (cached : m B = i) :
    confined (perform m event) A B ∧ perform m event B = i := by
  cases event with
  | normal cursor next =>
    obtain ⟨hcursor, hnext⟩ := ok
    refine ⟨confined_put onlyAt hnext, ?_⟩
    have noHit := Ne.symm (onlyAt cursor hcursor)
    simpa [perform, scan, put, noHit] using cached
  | exception addr value =>
    obtain ⟨haddr, hval⟩ := ok
    refine ⟨confined_put onlyAt hval, ?_⟩
    simpa [perform, put, Ne.symm haddr] using cached
  | skip => exact ⟨onlyAt, cached⟩

theorem survives_span {A B i : α} (events : List (Event α)) (m : α → α)
    (ok : ∀ e ∈ events, safe A B e) (onlyAt : confined m A B) (cached : m B = i) :
    confined (run m events) A B ∧ run m events B = i := by
  induction events generalizing m with
  | nil => exact ⟨onlyAt, cached⟩
  | cons e rest ih =>
    obtain ⟨onlyAt', cached'⟩ := survives_event e (ok e (by simp)) onlyAt cached
    exact ih (perform m e) (fun f hf => ok f (by simp [hf])) onlyAt' cached'

/-- At A the anchor contains its private marker B. Its forced write caches
    i in cell B. After arbitrarily many safe events, the one scheduled
    predecessor of B may itself write label B; this does not hit cell B.
    The step at B therefore writes its public successor onto the private cell i. -/
theorem erases_at_marker {m : α → α} {A B i before after : α}
    (events : List (Event α)) (anchor : m A = B) (onlyAt : confined m A B)
    (distinct : i ≠ B) (pre : before ≠ A) (ok : ∀ e ∈ events, safe A B e) :
    let middle := run (scan m A i) events
    let entering := scan middle before B
    entering B = i ∧ scan entering B after i = after := by
  have base : confined (scan m A i) A B := confined_put onlyAt distinct
  have cached : scan m A i B = i := by simp [scan, put, anchor]
  obtain ⟨hMid, hCache⟩ := survives_span events (scan m A i) ok base cached
  have noHit := Ne.symm (hMid before pre)
  have hFinal : scan (run (scan m A i) events) before B B = i := by
    change (if B = run (scan m A i) events before then B else _) = i
    rw [if_neg noHit]
    exact hCache
  refine ⟨hFinal, ?_⟩
  change (if i = scan (run (scan m A i) events) before B B then after else _) = after
  rw [if_pos hFinal.symm]

end ShiftedStrideOrigin
