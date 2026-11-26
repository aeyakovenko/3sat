import Std

/-! Local checks and correction of the first failed prediction in a causal stream. -/

namespace ForecastFirstDefect

abbrev Stream := Nat → Bool
abbrev Rule := Nat → Stream → Bool

/-- The rule at tick t can inspect only ticks strictly earlier than t.
    Fixed seed values at negative times can be built into the rule. -/
def Causal (r : Rule) : Prop :=
  ∀ t x y, (∀ i < t, x i = y i) → r t x = r t y

def Follows (x : Stream) (r : Rule) : Prop := ∀ t, x t = r t x

def run (r : Rule) (t : Nat) : Bool :=
  r t (fun i => if _h : i < t then run r i else false)
termination_by t

theorem run_follows {r : Rule} (hr : Causal r) : Follows (run r) r := by
  intro t
  rw [run]
  apply hr
  intro i hi
  simp [hi]

/-- Passing the genuine local comparison everywhere before the cut implies
    agreement with the genuine stream everywhere before that cut. -/
theorem agree_before {r : Rule} {actual candidate : Stream} {cut : Nat}
    (hr : Causal r) (truth : Follows actual r)
    (passes : ∀ i < cut, candidate i = r i candidate) :
    ∀ i < cut, candidate i = actual i := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    calc
      candidate i = r i candidate := passes i hi
      _ = r i actual := hr i candidate actual (fun j hj => ih j hj (Nat.lt_trans hj hi))
      _ = actual i := (truth i).symm

def withImpulses (predictor : Rule) (errors : Stream) : Rule :=
  fun t x => Bool.xor (predictor t x) (errors t)

theorem impulses_causal {p : Rule} (hp : Causal p) (e : Stream) :
    Causal (withImpulses p e) := by
  intro t x y prev
  simp only [withImpulses, hp t x y prev]

def toggleAt (e : Stream) (cut : Nat) : Stream :=
  fun i => if i = cut then !(e i) else e i

def residual (p : Rule) (actual : Stream) (i : Nat) : Bool :=
  Bool.xor (p i actual) (actual i)

/-- A failed genuine local comparison at the first defect identifies the
    actual erroneous impulse bit, even though the test used only the candidate. -/
theorem first_defect {r p : Rule} {e actual candidate : Stream} {cut : Nat}
    (hr : Causal r) (hp : Causal p) (truth : Follows actual r)
    (model : Follows candidate (withImpulses p e))
    (passes : ∀ i < cut, candidate i = r i candidate)
    (fails : candidate cut ≠ r cut candidate) :
    candidate cut ≠ actual cut ∧ e cut ≠ residual p actual cut := by
  have prev := agree_before hr truth passes
  have next : r cut candidate = actual cut := (hr cut _ _ prev).trans (truth cut).symm
  have wrong : candidate cut ≠ actual cut := fun h => fails (h.trans next.symm)
  refine ⟨wrong, ?_⟩
  have value := model cut
  rw [withImpulses, hp cut _ _ prev] at value
  intro equal
  apply wrong
  rw [value, equal, residual]
  cases p cut actual <;> cases actual cut <;> rfl

private theorem correct_by_toggling (prediction impulse truth : Bool)
    (wrong : Bool.xor prediction impulse ≠ truth) :
    Bool.xor prediction (!impulse) = truth := by
  revert wrong
  cases prediction <;> cases impulse <;> cases truth <;> decide

/-- Recompute the predictor with just the impulse at cut toggled. Its
    entire prefix through cut agrees with the actual stream. -/
theorem repair_first_defect {r p : Rule} {e actual candidate : Stream} {cut : Nat}
    (hr : Causal r) (hp : Causal p) (truth : Follows actual r)
    (model : Follows candidate (withImpulses p e))
    (passes : ∀ i < cut, candidate i = r i candidate)
    (fails : candidate cut ≠ r cut candidate) :
    ∀ i < cut + 1, run (withImpulses p (toggleAt e cut)) i = actual i := by
  let repaired := run (withImpulses p (toggleAt e cut))
  have recomputed : Follows repaired (withImpulses p (toggleAt e cut)) :=
    run_follows (impulses_causal hp _)
  have oldPrefix : ∀ i < cut, repaired i = candidate i := by
    apply agree_before (impulses_causal hp e) model
    intro i hi
    simpa [withImpulses, toggleAt, Nat.ne_of_lt hi] using recomputed i
  have actualPrefix := agree_before hr truth passes
  have wrong := (first_defect hr hp truth model passes fails).1
  have old := model cut
  have new := recomputed cut
  rw [withImpulses, hp cut _ _ oldPrefix] at new
  simp only [toggleAt, if_pos rfl] at new
  rw [withImpulses] at old
  have fixed : repaired cut = actual cut := by
    rw [old] at wrong
    rw [new]
    exact correct_by_toggling _ _ _ wrong
  intro i hi
  change repaired i = actual i
  by_cases earlier : i < cut
  · exact (oldPrefix i earlier).trans (actualPrefix i earlier)
  · have eq : i = cut := by omega
    exact eq ▸ fixed

end ForecastFirstDefect
