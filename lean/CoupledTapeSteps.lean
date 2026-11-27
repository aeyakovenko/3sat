import Std

namespace CoupledTapeSteps

/-- Each head has its own tape, even if two heads have the same coordinate. -/
structure Row (Head Key Inst CPU Value : Type) where
  instruction : Inst
  cpuIn : CPU
  cpuOut : CPU
  atCell : Head → Key
  before : Head → Value
  after : Head → Value

variable {H K I C V : Type} [DecidableEq K]
abbrev Memory (H K V : Type) := H → K → V

private def applyWrites (mem : Memory H K V) (keys : H → K) (vals : H → V) :
    Memory H K V :=
  fun h k => if k = keys h then vals h else mem h k

private def reads (mem : Memory H K V) (keys : H → K) : H → V :=
  fun h => mem h (keys h)

def cpuChain (cpu : C) : List (Row H K I C V) → Prop
  | [] => True
  | r :: rs => cpu = r.cpuIn ∧ cpuChain r.cpuOut rs

def cellChain (head : H) (key : K) (value : V) : List (Row H K I C V) → Prop
  | [] => True
  | r :: rs =>
    if key = r.atCell head then
      value = r.before head ∧ cellChain head key (r.after head) rs
    else cellChain head key value rs

private def run (loc : I → C → H → K) (step : I → C → (H → V) → Option (C × (H → V)))
    (cpu : C) (mem : Memory H K V) : List (Row H K I C V) → Option (C × Memory H K V)
  | [] => some (cpu, mem)
  | r :: rs => do
    let keys := loc r.instruction cpu
    let (nextCPU, vals) ← step r.instruction cpu (reads mem keys)
    run loc step nextCPU (applyWrites mem keys vals) rs

private def endState (cpu : C) (mem : Memory H K V) :
    List (Row H K I C V) → C × Memory H K V
  | [] => (cpu, mem)
  | r :: rs => endState r.cpuOut (applyWrites mem r.atCell r.after) rs

/-- The controller may depend jointly on every symbol read before writing any
    tape. Verifying each cell's chronology and each claimed controller transition
    forces all simultaneous observations and writes to be genuine. -/
theorem glue (loc : I → C → H → K) (step : I → C → (H → V) → Option (C × (H → V)))
    (cpu : C) (mem : Memory H K V) (rows : List (Row H K I C V))
    (legal : ∀ r ∈ rows, loc r.instruction r.cpuIn = r.atCell ∧
      step r.instruction r.cpuIn r.before = some (r.cpuOut, r.after))
    (cpuOk : cpuChain cpu rows)
    (cellsOk : ∀ h k, cellChain h k (mem h k) rows) :
    run loc step cpu mem rows = some (endState cpu mem rows) := by
  induction rows generalizing cpu mem with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨atCPU, laterCPU⟩ := cpuOk
    obtain ⟨atKeys, transition⟩ := legal r (List.mem_cons_self ..)
    have obs : reads mem r.atCell = r.before := by
      funext h
      have here := cellsOk h (r.atCell h)
      simp only [cellChain, if_pos rfl] at here
      exact here.1
    have later : ∀ h k, cellChain h k (applyWrites mem r.atCell r.after h k) rs := by
      intro h k
      have here := cellsOk h k
      by_cases atKey : k = r.atCell h
      · simp only [cellChain, if_pos atKey] at here
        simpa [applyWrites, atKey] using here.2
      · simpa [cellChain, atKey, applyWrites] using here
    have next := ih r.cpuOut _ (fun row h => legal row (List.mem_cons_of_mem _ h)) laterCPU later
    simpa [run, endState, atCPU, atKeys, obs, transition] using next

/-- A parked head's logical symbol is its private register. -/
def overlay (backing : K → V) (parked : K) (symbol : V) : K → V :=
  fun k => if k = parked then symbol else backing k

theorem park_updates (backing : K → V) (parked : K) (old new : V) :
    overlay (overlay backing parked old) parked new = overlay backing parked new := by
  funext k
  by_cases atHead : k = parked <;> simp [overlay, atHead]

/-- On departure, flush the updated old position and prefetch the destination.
    The resulting decoded tape agrees everywhere with the true updated tape. -/
theorem flush_and_fetch (backing : K → V) (src dst : K) (new : V) (moved : dst ≠ src) :
    overlay (overlay backing src new) dst (backing dst) = overlay backing src new := by
  funext k
  by_cases atDest : k = dst
  · subst k
    simp [overlay, moved]
  · simp [overlay, atDest]

omit [DecidableEq K] in
/-- Cache by occupied physical address rather than head identity. Updated values
    at old occupied cells already include the machine's simultaneous-write rule.
    Flushing departures and fetching arrivals preserves the whole logical tape,
    even if some heads collide or exchange occupied addresses. -/
theorem shared_cache_handoff (src dst : K → Bool) (back updated : K → V) :
    (fun k => if dst k then (if src k then updated k else back k)
                         else (if src k && !dst k then updated k else back k)) =
    (fun k => if src k then updated k else back k) := by
  funext k
  cases atSrc : src k <;> cases atDst : dst k <;> simp [atSrc, atDst]

end CoupledTapeSteps
