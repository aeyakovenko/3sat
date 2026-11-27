import Std

namespace TwoPrivateProbeSites

inductive Node where
  | first | second | yes | no | diverge
  deriving DecidableEq, Repr

def step (a b : Node) : Node → Node
  | .first => a
  | .second => b
  | q => q

def output : Node → Option Bool
  | .yes => some true
  | .no => some false
  | _ => none

def readout (a b : Node) : Nat → Node → Option Bool
  | 0, q => output q
  | k+1, q => readout a b k (step a b q)

theorem stable (a b q : Node) : readout a b 3 q = readout a b 2 q := by
  cases a <;> cases b <;> cases q <;> rfl

theorem stable_after_two (a b : Node) (k : Nat) (q : Node) :
    readout a b (k+2) q = readout a b 2 q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    calc
      readout a b (k+1+2) q = readout a b (k+2) (step a b q) := rfl
      _ = readout a b 2 (step a b q) := ih _
      _ = readout a b 2 q := stable a b q

theorem output_persists (a b q : Node) (v : Bool) (h : output q = some v) :
    output (step a b q) = some v := by
  cases q <;> simp_all [output, step]

theorem halting_visible_at_two (a b q : Node) (v : Bool) (k : Nat)
    (h : readout a b k q = some v) : readout a b 2 q = some v := by
  cases k with
  | zero => exact output_persists a b _ v (output_persists a b q v h)
  | succ k =>
    cases k with
    | zero => exact output_persists a b _ v h
    | succ k => exact (stable_after_two a b k q).symm.trans h

/-- With one query vertex per input bit, no cyclic graph decides equality.
    The four targets a0,a1,b0,b1 are arbitrary, as is the starting vertex. -/
theorem cannot_decide_eq (q a0 a1 b0 b1 : Node) :
    ¬ (∀ u v : Bool, ∃ k,
        readout (if u then a1 else a0) (if v then b1 else b0) k q = some (u == v)) := by
  intro h
  have check (u v : Bool) := (h u v).elim (fun k hk =>
    halting_visible_at_two _ _ _ _ k hk)
  have h00 := check false false
  have h01 := check false true
  have h10 := check true false
  have h11 := check true true
  have finite_check : ∀ q' a a' b b' : Node,
      ¬ (readout a b 2 q' = some true ∧ readout a b' 2 q' = some false ∧
         readout a' b 2 q' = some false ∧ readout a' b' 2 q' = some true) := by
    intro q' a a' b b'
    cases q' <;> cases a <;> cases a' <;> cases b <;> cases b' <;> decide
  exact finite_check q a0 a1 b0 b1 ⟨h00, h01, h10, h11⟩

/-- Public steps may use arbitrary table-dependent state. Reaching a private
    site permits only the continuation for that site and the bit returned. -/
inductive PublicOp (σ : Type) where
  | internal (next : σ)
  | first
  | second
  | result (answer : Bool)

variable {σ : Type} (prog : σ → PublicOp σ)

inductive Reaches : σ → Node → Prop where
  | internal (h : prog s = .internal r) (tail : Reaches r node) : Reaches s node
  | first (h : prog s = .first) : Reaches s .first
  | second (h : prog s = .second) : Reaches s .second
  | yes (h : prog s = .result true) : Reaches s .yes
  | no (h : prog s = .result false) : Reaches s .no

private theorem reaches_unique {s n m} (h : Reaches prog s n) (j : Reaches prog s m) :
    n = m := by
  induction h generalizing m with
  | internal hs _ ih =>
    cases j with
    | internal hr rest =>
      rw [hs] at hr
      cases hr
      exact ih rest
    | first hf => simp_all
    | second hf => simp_all
    | yes hf => simp_all
    | no hf => simp_all
  | first hf => cases j <;> simp_all
  | second hf => cases j <;> simp_all
  | yes hf => cases j <;> simp_all
  | no hf => cases j <;> simp_all

private noncomputable def summarize (s : σ) : Node := by
  classical
  exact if h : ∃ n, Reaches prog s n then Classical.choose h else .diverge

private theorem summary_of {s n} (reachable : Reaches prog s n) :
    summarize prog s = n := by
  classical
  have found : ∃ k, Reaches prog s k := ⟨n, reachable⟩
  simp only [summarize, dif_pos found]
  exact reaches_unique prog (Classical.choose_spec found) reachable

private theorem summary_step {s r} (h : prog s = .internal r) :
    summarize prog s = summarize prog r := by
  classical
  by_cases hr : ∃ n, Reaches prog r n
  · obtain ⟨n, hn⟩ := hr
    exact (summary_of prog (.internal h hn)).trans (summary_of prog hn).symm
  · have hs : ¬ ∃ n, Reaches prog s n := by
      rintro ⟨n, hn⟩
      cases hn with
      | internal hp tail =>
        rw [h] at hp
        cases hp
        exact hr ⟨_, tail⟩
      | first hp => simp_all
      | second hp => simp_all
      | yes hp => simp_all
      | no hp => simp_all
    simp [summarize, hs, hr]

variable (afterFirst afterSecond : Bool → σ) (u v : Bool)

/-- This small-step relation grants any number of public steps before,
    between and after private probes. Only finite halts have derivations. -/
inductive MachineHalts : σ → Bool → Prop where
  | internal (h : prog s = .internal r) (tail : MachineHalts r b) : MachineHalts s b
  | first (h : prog s = .first) (tail : MachineHalts (afterFirst u) b) : MachineHalts s b
  | second (h : prog s = .second) (tail : MachineHalts (afterSecond v) b) : MachineHalts s b
  | result (h : prog s = .result b) : MachineHalts s b

private theorem graph_replays {s b}
    (h : MachineHalts prog afterFirst afterSecond u v s b) :
    ∃ k, readout (summarize prog (afterFirst u)) (summarize prog (afterSecond v))
      k (summarize prog s) = some b := by
  induction h with
  | internal hs _ ih => simpa only [summary_step prog hs] using ih
  | first hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k+1, ?_⟩
    rw [summary_of prog (.first hs)]
    exact hk
  | second hs _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k+1, ?_⟩
    rw [summary_of prog (.second hs)]
    exact hk
  | @result s answer hs =>
    refine ⟨0, ?_⟩
    cases answer with
    | false => rw [summary_of prog (s := s) (.no hs)]; rfl
    | true => rw [summary_of prog (s := s) (.yes hs)]; rfl

/-- A deterministic read-only machine whose state after either private load
    depends only on that site's identity and its bit cannot decide equality.
    Its state space, public transitions, elapsed time and adaptive choice
    of which site to revisit are unrestricted. -/
theorem machine_cannot_decide_eq (start : σ) :
    ¬ (∀ a b : Bool, MachineHalts prog afterFirst afterSecond a b start (a == b)) := by
  intro decides
  apply cannot_decide_eq (summarize prog start)
    (summarize prog (afterFirst false)) (summarize prog (afterFirst true))
    (summarize prog (afterSecond false)) (summarize prog (afterSecond true))
  intro a b
  cases a <;> cases b <;>
    exact graph_replays prog afterFirst afterSecond _ _ (decides _ _)

/-- Both signs of variable 1 occur with each of the three pairs of signs of
    variables 2 and 3 other than positive/positive. -/
def sixClauses (x y z : Bool) : Bool :=
  (x || !y || z) && (!x || !y || z) &&
  (x || y || !z) && (!x || y || !z) &&
  (x || !y || !z) && (!x || !y || !z)

theorem six_force_false (x y z : Bool) : sixClauses x y z = (!y && !z) := by
  cases x <;> cases y <;> cases z <;> decide

/-- The two remaining clauses have positive literals on variables 2 and 3
    and private signs on variable 1. Here true denotes a positive sign. -/
def satEight (a b : Bool) : Bool :=
  [false, true].any fun x => [false, true].any fun y => [false, true].any fun z =>
    sixClauses x y z && ((a == x) || y || z) && ((b == x) || y || z)

theorem satEight_eq (a b : Bool) : satEight a b = (a == b) := by
  cases a <;> cases b <;> decide

theorem machine_cannot_decide_eight (start : σ) :
    ¬ (∀ a b : Bool, MachineHalts prog afterFirst afterSecond a b start (satEight a b)) := by
  simpa only [satEight_eq] using machine_cannot_decide_eq prog afterFirst afterSecond start

structure Registers (PC word : Type) where
  pc : PC
  x : word
  y : word

/-- Any public register computation and branch is allowed. The sole LOAD
    reads address y, overwrites x, and goes to the fixed resume PC. -/
inductive CPUOp (σ : Type) where
  | localStep (next : σ)
  | load
  | result (answer : Bool)

variable {PC word : Type} [DecidableEq word]
variable (decode : Registers PC word → CPUOp (Registers PC word)) (resumePC : PC)

inductive CPUHalts (memory : word → word) : Registers PC word → Bool → Prop where
  | localStep (op : decode s = .localStep r) (tail : CPUHalts memory r b) :
      CPUHalts memory s b
  | load (op : decode s = .load)
      (tail : CPUHalts memory ⟨resumePC, memory s.y, s.y⟩ b) : CPUHalts memory s b
  | result (op : decode s = .result b) : CPUHalts memory s b

variable (base : word → word) (siteA siteB : word) (wordA wordB : Bool → word)

def twoWordMemory (a b : Bool) (p : word) : word :=
  if p = siteA then wordA a else if p = siteB then wordB b else base p

private def contractCPU (s : Registers PC word) : PublicOp (Registers PC word) :=
  match decode s with
  | .localStep r => .internal r
  | .result b => .result b
  | .load =>
    if s.y = siteA then .first
    else if s.y = siteB then .second
    else .internal ⟨resumePC, base s.y, s.y⟩

private theorem cpu_to_machine {a b s answer}
    (h : CPUHalts decode resumePC (twoWordMemory base siteA siteB wordA wordB a b) s answer) :
    MachineHalts (contractCPU decode resumePC base siteA siteB)
      (fun bit => ⟨resumePC, wordA bit, siteA⟩)
      (fun bit => ⟨resumePC, wordB bit, siteB⟩) a b s answer := by
  induction h with
  | localStep op _ ih => exact .internal (by simp [contractCPU, op]) ih
  | result op => exact .result (by simp [contractCPU, op])
  | @load s answer op _ ih =>
    by_cases atA : s.y = siteA
    · apply MachineHalts.first (by simp [contractCPU, op, atA])
      simpa [twoWordMemory, atA] using ih
    · by_cases atB : s.y = siteB
      · have sitesNe : siteB ≠ siteA := by simpa only [atB] using atA
        apply MachineHalts.second (by simp [contractCPU, op, atB, sitesNe])
        simpa [twoWordMemory, atB, sitesNe] using ih
      · apply MachineHalts.internal (r := ⟨resumePC, base s.y, s.y⟩)
          (by simp [contractCPU, op, atA, atB])
        simpa [twoWordMemory, atA, atB] using ih

/-- A single fixed-successor LOAD into x through y cannot decide the four
    eight-clause formulas when the files differ only at their two sign
    words. Arbitrary public state initialization at this length is allowed;
    the initial PC and registers must agree across the four files. -/
theorem cpu_cannot_decide_eight (start : Registers PC word) :
    ¬ (∀ a b, CPUHalts decode resumePC
      (twoWordMemory base siteA siteB wordA wordB a b) start (satEight a b)) := by
  intro decides
  apply machine_cannot_decide_eight (contractCPU decode resumePC base siteA siteB)
    (fun bit => ⟨resumePC, wordA bit, siteA⟩) (fun bit => ⟨resumePC, wordB bit, siteB⟩) start
  exact fun a b => cpu_to_machine decode resumePC base siteA siteB wordA wordB (decides a b)

/-- The four literal files at the width-16 witness length; true is positive.
    All characters belong to ASCII, for which character and byte values agree. -/
def sampleBytes (a b : Bool) : List Nat :=
  let publicText := "p cnf 3 8\n1 2 -3 0\n1 -2 3 0\n1 -2 -3 0\n" ++
    "-1 2 -3 0\n-1 -2 3 0\n-1 -2 -3 0\n"
  let sign (positive : Bool) := if positive then " " else "-"
  (publicText ++ sign a ++ "1 2 3 0\n" ++ sign b ++ "1 2 3 0\n").toList.map Char.toNat

theorem sample_length (a b : Bool) : (sampleBytes a b).length = 87 := by
  cases a <;> cases b <;> decide

def sampleMemory (a b : Bool) (address : Nat) : Nat :=
  if address < 44 then
    let bytes := sampleBytes a b
    bytes[2*address]?.getD 0 + 256 * bytes[2*address+1]?.getD 0
  else 0

theorem sample_layout (a b : Bool) :
    sampleMemory a b = twoWordMemory (sampleMemory true true) 34 39
      (fun bit => sampleMemory bit true 34) (fun bit => sampleMemory true bit 39) a b := by
  have finiteCheck : ∀ u v, ∀ j : Fin 44,
      sampleMemory u v j.val = twoWordMemory (sampleMemory true true) 34 39
        (fun bit => sampleMemory bit true 34) (fun bit => sampleMemory true bit 39)
        u v j.val := by decide
  funext j
  by_cases hj : j < 44
  · exact finiteCheck a b ⟨j, hj⟩
  · have ha : j ≠ 34 := by omega
    have hb : j ≠ 39 := by omega
    simp [twoWordMemory, ha, hb, sampleMemory, hj]

/-- Here the CPU is supplied the little-endian words of the four displayed
    files, with natural-number addresses and public zero scratch memory. -/
theorem cpu_cannot_decide_packed_sample
    (cpu : Registers PC Nat → CPUOp (Registers PC Nat))
    (resume : PC) (start : Registers PC Nat) :
    ¬ (∀ a b, CPUHalts cpu resume (sampleMemory a b) start (satEight a b)) := by
  intro h
  apply cpu_cannot_decide_eight cpu resume (sampleMemory true true) 34 39
    (fun bit => sampleMemory bit true 34) (fun bit => sampleMemory true bit 39) start
  intro a b
  rw [← sample_layout a b]
  exact h a b

end TwoPrivateProbeSites

namespace FiveSlotScratchSample
open TwoPrivateProbeSites

/-- A public step or STORE can choose its successor registers and PC. The
    LOAD reads through y into x and has one fixed successor PC. -/
inductive Op (σ word : Type) where
  | localStep (next : σ)
  | store (value : word) (next : σ)
  | load
  | result (answer : Bool)

variable {PC word : Type} [DecidableEq word]
abbrev Reg (PC word : Type) := Registers PC word
abbrev State (PC word : Type) := Reg PC word × Option word

/-- A single fixed writable cell is represented exactly by its last payload.
    No stores change the original memory outside that address. -/
def savedAt (scratch : word) (saved : Option word) (addr : word) : Option word :=
  if addr = scratch then saved else none

variable (cpu : Reg PC word → Op (Reg PC word) word) (resume : PC) (scratch : word)

/-- The Boolean is a trace predicate, unavailable to instructions. It starts
    true, is cleared by LOAD and is set by STORE. Thus finite halts require
    a STORE strictly between each two successive LOADs, and nowhere else. -/
inductive Halts (original : word → word) :
    Reg PC word → Option word → Bool → Bool → Prop where
  | localStep (op : cpu r = .localStep r') (tail : Halts original r' saved ready answer) :
      Halts original r saved ready answer
  | store (op : cpu r = .store value r') (tail : Halts original r' (some value) true answer) :
      Halts original r saved ready answer
  | load (op : cpu r = .load)
      (tail : Halts original
        ⟨resume, (savedAt scratch saved r.y).getD (original r.y), r.y⟩ saved false answer) :
      Halts original r saved true answer
  | result (op : cpu r = .result answer) : Halts original r saved ready answer

private def afterLoad (pc : PC) (addr value : word) : State PC word :=
  (⟨pc, value, addr⟩, none)

private def project (r : Reg PC word) (saved : Option word) (ready : Bool) : State PC word :=
  (r, if ready then saved else none)

variable (base : word → word) (A B : word) (wordA wordB : Bool → word)

/-- On a real trace, any scratch value discarded at a LOAD will be
    overwritten before it can be read. A hit on a stored scratch value
    is therefore a public step even when the scratch is A or B. -/
private def contract (s : State PC word) : PublicOp (State PC word) :=
  match cpu s.1 with
  | .localStep r => .internal (r, s.2)
  | .store v r => .internal (r, some v)
  | .result ans => .result ans
  | .load =>
    match savedAt scratch s.2 s.1.y with
    | some v => .internal (afterLoad resume s.1.y v)
    | none =>
      if s.1.y = A then .first
      else if s.1.y = B then .second
      else .internal (afterLoad resume s.1.y (base s.1.y))

private theorem replay {a b : Bool} {r : Reg PC word} {saved : Option word} {ready answer : Bool}
    (h : Halts cpu resume scratch (twoWordMemory base A B wordA wordB a b) r saved ready answer) :
    MachineHalts (contract cpu resume scratch base A B)
      (fun bit => afterLoad resume A (wordA bit)) (fun bit => afterLoad resume B (wordB bit))
      a b (project r saved ready) answer := by
  induction h with
  | localStep op _ ih =>
    exact .internal (by simp [contract, project, op]) ih
  | store op _ ih =>
    exact .internal (by simp [contract, project, op]) ih
  | result op => exact .result (by simp [contract, project, op])
  | @load r saved answer op _ ih =>
    cases hs : savedAt scratch saved r.y with
    | some val =>
      apply MachineHalts.internal (r := afterLoad resume r.y val) (by simp [contract, project, op, hs])
      simpa [project, afterLoad, hs] using ih
    | none =>
      by_cases ha : r.y = A
      · have hsA : savedAt scratch saved A = none := ha ▸ hs
        apply MachineHalts.first (by simp [contract, project, op, ha, hsA])
        simpa [project, afterLoad, twoWordMemory, ha, hsA] using ih
      · by_cases hb : r.y = B
        · have hba : B ≠ A := by simpa only [hb] using ha
          have hsB : savedAt scratch saved B = none := hb ▸ hs
          apply MachineHalts.second (by simp [contract, project, op, hb, hsB, hba])
          simpa [project, afterLoad, twoWordMemory, hb, hsB, hba] using ih
        · apply MachineHalts.internal (r := afterLoad resume r.y (base r.y))
            (by simp [contract, project, op, hs, ha, hb])
          simpa [project, afterLoad, hs, twoWordMemory, ha, hb] using ih

/-- All scratch addresses are covered, including the two private words. -/
theorem cannot_decide_eight (start : Reg PC word) :
    ¬ (∀ a b, Halts cpu resume scratch (twoWordMemory base A B wordA wordB a b)
      start none true (satEight a b)) := by
  intro h
  apply machine_cannot_decide_eight (contract cpu resume scratch base A B)
    (fun bit => afterLoad resume A (wordA bit)) (fun bit => afterLoad resume B (wordB bit))
    (project start none true)
  exact fun a b => replay cpu resume scratch base A B wordA wordB (h a b)

/-- The literal 87-byte little-endian DIMACS samples defeat every program
    in the class at every choice of its fixed scratch address. -/
theorem cannot_decide_packed_sample
    (machine : Reg PC Nat → Op (Reg PC Nat) Nat) (resumePC : PC)
    (addr : Nat) (start : Reg PC Nat) :
    ¬ (∀ a b, Halts machine resumePC addr (sampleMemory a b)
      start none true (satEight a b)) := by
  intro h
  apply cannot_decide_eight machine resumePC addr (sampleMemory true true) 34 39
    (fun bit => sampleMemory bit true 34) (fun bit => sampleMemory true bit 39) start
  intro a b
  rw [← sample_layout a b]
  exact h a b

end FiveSlotScratchSample
