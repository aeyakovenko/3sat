import Std

/-! Semantics of checkpoint verification for a bounded deterministic word
machine. A segment can choose arbitrary addresses adaptively and overwrite
them. Its deterministic register arithmetic is part of the continuations.
The decoder of a shared pool may give a different word for each checkpoint
and address. The lemmas impose no encoding length or evaluation-time bound.
-/

namespace SolverSnapshotReplay

abbrev Memory (Address Word : Type) := Address → Word
abbrev State (Address Word Control : Type) := Control × Memory Address Word

inductive Segment (Address Word Control : Type) where
  | done (control : Control)
  | read (address : Address) (next : Word → Segment Address Word Control)
  | write (address : Address) (value : Word) (next : Segment Address Word Control)

def store [DecidableEq A] (mem : Memory A W) (addr : A) (word : W) : Memory A W :=
  fun a => if a = addr then word else mem a

def replay [DecidableEq A] : Segment A W C → Memory A W → State A W C
  | .done c, mem => (c, mem)
  | .read addr next, mem => replay (next (mem addr)) mem
  | .write addr word next, mem => replay next (store mem addr word)

def observe (probe : Option A) (s : State A W C) : C × Option W :=
  (s.1, probe.map s.2)

/-- Incoming words actually consulted on this execution, including an
optional observation of one address at its end. An earlier write masks
that address in the remaining execution. -/
def consulted [DecidableEq A] (probe : Option A) :
    Segment A W C → Memory A W → A → Prop
  | .done _, _, a => probe = some a
  | .read addr next, mem, a =>
    a = addr ∨ consulted probe (next (mem addr)) mem a
  | .write addr word next, mem, a =>
    a ≠ addr ∧ consulted probe next (store mem addr word) a

/-- It suffices that the supplied incoming words agree on the words queried
on one execution. The second execution then takes the same adaptive path
and produces the same exit control and optional terminal word. -/
theorem replayObservation [DecidableEq A] (seg : Segment A W C) (probe : Option A)
    (actual supplied : Memory A W)
    (h : ∀ a, consulted probe seg actual a → actual a = supplied a) :
    observe probe (replay seg actual) = observe probe (replay seg supplied) := by
  induction seg generalizing actual supplied with
  | done c =>
    cases probe with
    | none => rfl
    | some a =>
      have hw := h a rfl
      simp [observe, replay, hw]
  | read addr next ih =>
    have hw := h addr (Or.inl rfl)
    have tail := ih (actual addr) actual supplied (fun a ha => h a (Or.inr ha))
    change observe probe (replay (next (actual addr)) actual) =
      observe probe (replay (next (supplied addr)) supplied)
    rwa [← hw]
  | write addr word next ih =>
    apply ih
    intro a ha
    by_cases same : a = addr
    · simp [store, same]
    · simpa only [store, if_neg same] using h a ⟨same, ha⟩

/-- Verifying the control and the value of an arbitrary single addressed
word pointwise establishes equality of whole states, including untouched
cells. -/
def pointCheck (s t : State A W C) : Prop :=
  s.1 = t.1 ∧ ∀ a, s.2 a = t.2 a

theorem pointCheckIff (s t : State A W C) : pointCheck s t ↔ s = t := by
  constructor
  · rintro ⟨ctrl, words⟩
    exact Prod.ext ctrl (funext words)
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩

/-- The segment code can depend on the public segment index and the
incoming registers, including the program counter. -/
def trajectory [DecidableEq A] (code : Nat → C → Segment A W C)
    (initial : State A W C) : Nat → State A W C
  | 0 => initial
  | i+1 =>
    let s := trajectory code initial i
    replay (code i s.1) s.2

def checks [DecidableEq A] (code : Nat → C → Segment A W C) (initial : State A W C)
    (cuts : Nat → State A W C) (k : Nat) : Prop :=
  pointCheck (cuts 0) initial ∧
    ∀ i, i < k → pointCheck (replay (code i (cuts i).1) (cuts i).2) (cuts (i+1))

theorem checkedTrajectory [DecidableEq A] (code : Nat → C → Segment A W C)
    (initial : State A W C) (cuts : Nat → State A W C) (k : Nat)
    (valid : checks code initial cuts k) (i : Nat) (hi : i ≤ k) :
    cuts i = trajectory code initial i := by
  induction i with
  | zero => exact (pointCheckIff _ _).mp valid.1
  | succ i ih =>
    have hs := ((pointCheckIff _ _).mp (valid.2 i (by omega))).symm
    rw [ih (by omega)] at hs
    exact hs

/-- All checks using the same pool imply the claimed terminal verdict,
for either Boolean sign. Soundness is independent of which pools are
short or which distributions of addresses the actual solver uses. -/
theorem signedPoolSound [DecidableEq A] (decode : Pool → Nat → State A W C)
    (code : Nat → C → Segment A W C) (initial : State A W C) (k : Nat)
    (sign : C → Bool) (claimed : Bool) (pool : Pool)
    (valid : checks code initial (decode pool) k)
    (terminal : sign (decode pool k).1 = claimed) :
    sign (trajectory code initial k).1 = claimed := by
  simpa only [checkedTrajectory code initial (decode pool) k valid k (Nat.le_refl k)] using terminal

/-- Completeness requires a pool that reproduces the true checkpoints.
With such a pool, the checks certify precisely the true final sign. -/
theorem signedPoolIff [DecidableEq A] (decode : Pool → Nat → State A W C)
    (code : Nat → C → Segment A W C) (initial : State A W C) (k : Nat)
    (sign : C → Bool) (claimed : Bool)
    (represented : ∃ pool, ∀ i, i ≤ k → decode pool i = trajectory code initial i) :
    (∃ pool, checks code initial (decode pool) k ∧ sign (decode pool k).1 = claimed) ↔
      sign (trajectory code initial k).1 = claimed := by
  constructor
  · rintro ⟨pool, valid, terminal⟩
    exact signedPoolSound decode code initial k sign claimed pool valid terminal
  · intro terminal
    obtain ⟨pool, rep⟩ := represented
    refine ⟨pool, ⟨?_, ?_⟩, ?_⟩
    · apply (pointCheckIff _ _).mpr
      exact rep 0 (Nat.zero_le _)
    · intro i hi
      apply (pointCheckIff _ _).mpr
      rw [rep i (by omega), rep (i+1) (by omega)]
      rfl
    · rwa [rep k (Nat.le_refl _)]

/-- External control records provide the registers. The first memory is
known; positive indices fetch an internal memory from the common pool. -/
def internalCuts (initial : State A W C) (decode : Pool → Nat → Memory A W)
    (pool : Pool) (registers : Nat → C) : Nat → State A W C
  | 0 => (registers 0, initial.2)
  | i+1 => (registers (i+1), decode pool (i+1))

/-- There are last+1 segments. A transition to an internal endpoint is
checked at every address; the final segment checks only registers and sign. -/
def signedInternal [DecidableEq A] (code : Nat → C → Segment A W C)
    (initial : State A W C) (decode : Pool → Nat → Memory A W) (pool : Pool)
    (registers : Nat → C) (last : Nat) (sign : C → Bool) (claimed : Bool) : Prop :=
  let cuts := internalCuts initial decode pool registers
  checks code initial cuts last ∧
    (replay (code last (cuts last).1) (cuts last).2).1 = registers (last+1) ∧
    sign (registers (last+1)) = claimed

theorem signedInternalSound [DecidableEq A] {code : Nat → C → Segment A W C}
    {initial : State A W C} {decode : Pool → Nat → Memory A W} {pool : Pool}
    {registers : Nat → C} {last : Nat} {sign : C → Bool} {claimed : Bool}
    (h : signedInternal code initial decode pool registers last sign claimed) :
    sign (trajectory code initial (last+1)).1 = claimed := by
  obtain ⟨boundaries, endCtrl, endSign⟩ := h
  have eq := checkedTrajectory code initial _ last boundaries last (Nat.le_refl _)
  rw [eq] at endCtrl
  change (trajectory code initial (last+1)).1 = registers (last+1) at endCtrl
  rwa [endCtrl]

/-- Honest descriptions are needed only for indices 1 through last.
Neither an initial nor a final memory is requested from the decoder. -/
theorem signedInternalIff [DecidableEq A] (code : Nat → C → Segment A W C)
    (initial : State A W C) (decode : Pool → Nat → Memory A W) (pool : Pool)
    (last : Nat) (sign : C → Bool) (claimed : Bool)
    (represented : ∀ i, i < last →
      decode pool (i+1) = (trajectory code initial (i+1)).2) :
    (∃ registers, signedInternal code initial decode pool registers last sign claimed) ↔
      sign (trajectory code initial (last+1)).1 = claimed := by
  constructor
  · rintro ⟨registers, accepted⟩
    exact signedInternalSound accepted
  · intro verdict
    let registers (i : Nat) := (trajectory code initial i).1
    let cuts := internalCuts initial decode pool registers
    have honest (i : Nat) (hi : i ≤ last) : cuts i = trajectory code initial i := by
      cases i with
      | zero => rfl
      | succ i => exact Prod.ext rfl (represented i (by omega))
    refine ⟨registers, ⟨?_, ?_⟩, ?_, verdict⟩
    · apply (pointCheckIff _ _).mpr
      rfl
    · intro i hi
      apply (pointCheckIff _ _).mpr
      change replay (code i (cuts i).1) (cuts i).2 = cuts (i+1)
      rw [honest i (by omega), honest (i+1) (by omega)]
      rfl
    · change (replay (code last (cuts last).1) (cuts last).2).1 = registers (last+1)
      rw [honest last (Nat.le_refl _)]
      rfl

/-- An observation concerns a single branch at a specific time at or
before the clock. No bound on other branches is part of this definition. -/
def observedBy (signal : Branch → Nat → Prop) (clock : Nat) : Prop :=
  ∃ branch time, time ≤ clock ∧ signal branch time

/-- Logical diagonal consequence for one fixed padded source input. The
external reduction identifies SAT with an observed signal; checker
soundness gives the opposite sign on each success. The separate time
hypothesis is required only for an honest short rejection certificate. -/
theorem signedClockDiagonal (satisfiable : Prop) (signal : Branch → Nat → Prop)
    (clock cutoff : Nat) (honest : Cert → Prop) (size : Cert → Nat)
    (sourceEncoding : satisfiable ↔ observedBy signal clock)
    (successMeansReject : ∀ branch time, signal branch time → ¬ satisfiable)
    (shortRejectInTime : ¬ satisfiable → ∀ cert, honest cert → size cert ≤ cutoff →
      observedBy signal clock) :
    ¬ satisfiable ∧ ¬ observedBy signal clock ∧ ∀ cert, honest cert → cutoff < size cert := by
  have unsat : ¬ satisfiable := by
    intro sat
    obtain ⟨b, t, _, success⟩ := sourceEncoding.mp sat
    exact successMeansReject b t success sat
  have unseen : ¬ observedBy signal clock := fun seen => unsat (sourceEncoding.mpr seen)
  refine ⟨unsat, unseen, ?_⟩
  intro cert real
  by_cases short : size cert ≤ cutoff
  · exact False.elim (unseen (shortRejectInTime unsat cert real short))
  · omega

/-- At pool length N/L^(a+4) bits, the pool work has the same order as
the source clock H (N scales as H L^3). The short-certificate implication
therefore additionally needs a sufficiently small constant. The replay has
an entire logarithm of slack. -/
theorem snapshotCost (a d : Int) :
    (a+3)-(2*a+d+7)+(a+d+3) = -1 ∧
    3-(a+4)+(a+1) = 0 := by omega

end SolverSnapshotReplay
