import Std

namespace HybridTileCuts

/-- The CPU includes the full sparse random-access array. A tile carries the separate
    contents of one geometric region. Each instruction here is one checked segment. -/
structure Boundary (Key Instruction CPU Tile : Type) where
  key : Key
  instruction : Instruction
  cpuIn : CPU
  cpuOut : CPU
  tileIn : Tile
  tileOut : Tile

variable {K I C V : Type} [DecidableEq K]

private def store (tiles : K → V) (key : K) (value : V) : K → V :=
  fun k => if k = key then value else tiles k

def cpuChain (cpu : C) : List (Boundary K I C V) → Prop
  | [] => True
  | h :: tail => cpu = h.cpuIn ∧ cpuChain h.cpuOut tail

/-- Check a tile along its own chronological subsequence, skipping every other tile. -/
def tileChain (key : K) (value : V) : List (Boundary K I C V) → Prop
  | [] => True
  | h :: tail =>
    if key = h.key then value = h.tileIn ∧ tileChain key h.tileOut tail
    else tileChain key value tail

/-- Global replay uses only the real CPU state and the current contents of the selected
    tile. A bad crossing or instruction may produce no result. -/
def run (step : I → C → V → Option (C × V)) (cpu : C) (tiles : K → V) :
    List (Boundary K I C V) → Option (C × (K → V))
  | [] => some (cpu, tiles)
  | h :: tail => do
    let (cpu', value) ← step h.instruction cpu (tiles h.key)
    run step cpu' (store tiles h.key value) tail

private def declaredEnd (cpu : C) (tiles : K → V) :
    List (Boundary K I C V) → C × (K → V)
  | [] => (cpu, tiles)
  | h :: tail => declaredEnd h.cpuOut (store tiles h.key h.tileOut) tail

/-- Agreement along the single CPU chain and along each separate tile chain glues
    checked local segment replays into the unique forward global computation. -/
theorem glue (step : I → C → V → Option (C × V)) (cpu : C) (tiles : K → V)
    (segments : List (Boundary K I C V))
    (legal : ∀ h ∈ segments, step h.instruction h.cpuIn h.tileIn = some (h.cpuOut, h.tileOut))
    (chronological : cpuChain cpu segments)
    (geometric : ∀ k, tileChain k (tiles k) segments) :
    run step cpu tiles segments = some (declaredEnd cpu tiles segments) := by
  induction segments generalizing cpu tiles with
  | nil => rfl
  | cons h tail ih =>
    obtain ⟨sameCPU, laterCPU⟩ := chronological
    have here := geometric h.key
    simp only [tileChain, if_pos rfl] at here
    have laterTile : ∀ k, tileChain k (store tiles h.key h.tileOut k) tail := by
      intro k
      by_cases eq : k = h.key
      · subst k
        simpa [store] using here.2
      · simpa [store, tileChain, eq] using geometric k
    have first := legal h (List.mem_cons_self ..)
    have later := ih h.cpuOut (store tiles h.key h.tileOut)
      (fun elt inTail => legal elt (List.mem_cons_of_mem _ inTail)) laterCPU laterTile
    simpa [run, declaredEnd, sameCPU, here.1, first] using later

end HybridTileCuts
