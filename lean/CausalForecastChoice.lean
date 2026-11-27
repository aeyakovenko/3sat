import Std

namespace CausalForecastChoice

/-- A forecast is observed before choosing a bit. The state may contain the
    remaining hit and alarm quotas and the entire observed history. -/
structure Game (State Forecast Expert : Type) where
  capacity : Nat → State → Nat
  badCount : Nat → State → Nat
  legal : Nat → State → Forecast → Prop
  next : Nat → State → Forecast → Bool → State
  badAtEnd : State → Expert → Prop
  capacitySplit : ∀ n x f, legal n x f →
    capacity (n+1) x =
      capacity n (next n x f false) + capacity n (next n x f true)
  badSplit : ∀ n x f, legal n x f →
    badCount (n+1) x =
      badCount n (next n x f false) + badCount n (next n x f true)
  terminalCapacity : ∀ x, capacity 0 x ≤ 1
  terminalBad : ∀ x e, 0 < capacity 0 x → badAtEnd x e → 0 < badCount 0 x

variable {State Forecast Expert : Type} (g : Game State Forecast Expert)

/-- Choose zero if it has strict slack after seeing this forecast. -/
def pick (n : Nat) (x : State) (f : Forecast) : Bool :=
  if g.badCount n (g.next n x f false) < g.capacity n (g.next n x f false)
  then false else true

theorem keepSlack (n : Nat) (x : State) (f : Forecast) (hf : g.legal n x f)
    (hx : g.badCount (n+1) x < g.capacity (n+1) x) :
    g.badCount n (g.next n x f (pick g n x f)) <
    g.capacity n (g.next n x f (pick g n x f)) := by
  rw [g.badSplit n x f hf, g.capacitySplit n x f hf] at hx
  unfold pick
  split <;> omega

/-- Every state reached has positive capacity and strict slack. The universal
    quantifier permits the next forecast to depend on all previous choices. -/
def Safe : Nat → State → Prop
  | 0, x => g.capacity 0 x = 1 ∧ g.badCount 0 x = 0 ∧ ∀ e, ¬g.badAtEnd x e
  | n+1, x => 0 < g.capacity (n+1) x ∧ g.badCount (n+1) x < g.capacity (n+1) x ∧
      ∀ f, g.legal n x f → Safe n (g.next n x f (pick g n x f))

theorem online (n : Nat) (x : State) (hx : g.badCount n x < g.capacity n x) :
    Safe g n x := by
  induction n generalizing x with
  | zero =>
    have hcap := g.terminalCapacity x
    refine ⟨by omega, by omega, ?_⟩
    intro e he
    have := g.terminalBad x e (by omega) he
    omega
  | succ n ih =>
    exact ⟨by omega, hx, fun f hf => ih _ (keepSlack g n x f hf hx)⟩

/-- Number of completions with exactly 'target' total hits, when 'used'
    positions were selected earlier. This handles zero remaining hits and
    infeasible branches without truncated subtraction. -/
def capacity (target : Nat) : Nat → Nat → Nat
  | 0, used => if used = target then 1 else 0
  | n+1, used => capacity target n used + capacity target n (used+1)

theorem feasibleEnd (target used : Nat) : capacity target 0 used = 1 ↔ used = target := by
  simp [capacity]

/-- Count one expert's bad completions from the hit total and overlap so far.
    A selected position increments overlap precisely when its alarm is set. -/
def score (target : Nat) (bad : Nat → Bool) : List Bool → Nat → Nat → Nat
  | [], used, hits => if used = target ∧ bad hits = true then 1 else 0
  | f::tail, used, hits =>
    score target bad tail used hits +
    score target bad tail (used+1) (hits + f.toNat)

/-- The score depends only on the multiplicities of the remaining flags. -/
theorem permScore (target : Nat) (bad : Nat → Bool) {u v : List Bool} (hp : u.Perm v) :
    ∀ used hits, score target bad u used hits = score target bad v used hits := by
  induction hp with
  | nil => simp
  | cons _ hp ih =>
    intro used hits
    simp only [score, ih]
  | swap a b tail =>
    intro used hits
    simp only [score]
    have h : hits + a.toNat + b.toNat = hits + b.toNat + a.toNat := by omega
    rw [h]
    omega
  | trans _ _ ih₁ ih₂ =>
    intro used hits
    exact (ih₁ used hits).trans (ih₂ used hits)

/-- A forecast can choose either first flag consistent with its exact quota.
    The unobserved order of the remaining flags may change at the next step. -/
theorem scoreSplit (target : Nat) (bad : Nat → Bool)
    (remaining tail : List Bool) (flag : Bool)
    (quota : remaining.Perm (flag :: tail)) (used hits : Nat) :
    score target bad remaining used hits =
      score target bad tail used hits +
      score target bad tail (used+1) (hits + flag.toNat) := by
  exact permScore target bad quota used hits

/-- Sum the per-expert identities for a finite menu, allowing repetitions. -/
theorem sumSplit {E : Type} (experts : List E) (before left right : E → Nat)
    (splits : ∀ e ∈ experts, before e = left e + right e) :
    (experts.map before).sum = (experts.map left).sum + (experts.map right).sum := by
  induction experts with
  | nil => simp
  | cons e es ih =>
    have he := splits e (by simp)
    have hs := ih (fun a ha => splits a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons]
    omega

end CausalForecastChoice
