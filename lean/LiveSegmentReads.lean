import Std

/-! A finite deterministic load/store segment. The trace includes controller
states, addresses, loaded values and stored values. The final controller is
recorded separately. An instruction doing several operations can be split
into these elementary steps. -/

namespace LiveSegmentReads

inductive Instruction (Addr Word Control : Type) where
  | internal (next : Control)
  | load (address : Addr) (next : Word → Control)
  | store (address : Addr) (value : Word) (next : Control)

inductive Event (Addr Word : Type) where
  | internal
  | load (address : Addr) (value : Word)
  | store (address : Addr) (value : Word)

variable {Addr Word Control : Type} [DecidableEq Addr]

def write (mem : Addr → Word) (a : Addr) (v : Word) (b : Addr) : Word :=
  if b=a then v else mem b

structure Observation (Addr Word Control : Type) where
  trace : List (Control × Event Addr Word)
  finalControl : Control

def prepend (s : Control) (event : Event Addr Word) (tail : Observation Addr Word Control) :
    Observation Addr Word Control := ⟨(s,event)::tail.trace, tail.finalControl⟩

def run (code : Control → Instruction Addr Word Control) :
    Nat → Control → (Addr → Word) → Observation Addr Word Control
  | 0, s, _ => ⟨[], s⟩
  | n+1, s, mem =>
    match code s with
    | .internal next => prepend s .internal (run code n next mem)
    | .load a next => prepend s (.load a (mem a)) (run code n (next (mem a)) mem)
    | .store a v next => prepend s (.store a v) (run code n next (write mem a v))

/-- Scan the observed trace from the start. A prior store to this address
blocks every later load from imposing a condition on the initial word. -/
def incoming (address : Addr) : List (Control × Event Addr Word) → Prop
  | [] => False
  | (_, .internal)::rest => incoming address rest
  | (_, .load a _)::rest => a=address ∨ incoming address rest
  | (_, .store a _)::rest => a≠address ∧ incoming address rest

/-- The other memory need only agree on incoming loads of the *true* run.
Both runs then take the same controller transitions, including every
adaptive read and write, and finish in the same controller state. -/
theorem agreeOnIncoming (code : Control → Instruction Addr Word Control)
    (n : Nat) (s : Control) (mem other : Addr → Word)
    (agree : ∀ a, incoming a (run code n s mem).trace → mem a=other a) :
    run code n s mem = run code n s other := by
  induction n generalizing s mem other with
  | zero => rfl
  | succ n ih =>
    cases hcode : code s with
    | internal next =>
      have tail := ih next mem other (fun a ha => agree a (by
        simpa only [run, hcode, prepend, incoming] using ha))
      simp only [run, hcode, tail]
    | load a next =>
      have word := agree a (by simp [run, hcode, prepend, incoming])
      have tail := ih (next (mem a)) mem other (fun b hb => agree b (by
        simp only [run, hcode, prepend, incoming]
        exact Or.inr hb))
      simp only [run, hcode]
      rw [←word, tail]
    | store a v next =>
      have tail := ih next (write mem a v) (write other a v) (by
        intro b hb
        by_cases same : b=a
        · simp [write, same]
        · have old := agree b (by
            simp only [run, hcode, prepend, incoming]
            exact ⟨Ne.symm same, hb⟩)
          simpa only [write, if_neg same] using old)
      simp only [run, hcode, tail]

/-- Look up the first observed load of this address before any local store
to it. An unqueried initial word has no recorded value. -/
def initialReply (address : Addr) : List (Control × Event Addr Word) → Option Word
  | [] => none
  | (_, .internal)::rest => initialReply address rest
  | (_, .load a v)::rest => if a=address then some v else initialReply address rest
  | (_, .store a _)::rest => if a=address then none else initialReply address rest

/-- An incoming read's value is identifiable from the trace alone. -/
theorem incomingReply (code : Control → Instruction Addr Word Control)
    (n : Nat) (s : Control) (mem : Addr → Word) (a : Addr)
    (used : incoming a (run code n s mem).trace) :
    initialReply a (run code n s mem).trace = some (mem a) := by
  induction n generalizing s mem with
  | zero => exact used.elim
  | succ n ih =>
    cases hcode : code s with
    | internal next =>
      simp only [run, hcode, prepend, incoming, initialReply] at used ⊢
      exact ih next mem used
    | load b next =>
      simp only [run, hcode, prepend, incoming, initialReply] at used ⊢
      by_cases same : b=a
      · simp [same]
      · rw [if_neg same]
        exact ih (next (mem b)) mem (used.resolve_left same)
    | store b v next =>
      simp only [run, hcode, prepend, incoming, initialReply] at used ⊢
      rw [if_neg used.1]
      simpa only [write, if_neg (Ne.symm used.1)] using ih next (write mem b v) used.2

/-- Exact dependency criterion, since observed loads retain their words. -/
theorem sameObservationIff (code : Control → Instruction Addr Word Control)
    (n : Nat) (s : Control) (mem other : Addr → Word) :
    run code n s mem = run code n s other ↔
      ∀ a, incoming a (run code n s mem).trace → mem a=other a := by
  constructor
  · intro eq a used
    have left := incomingReply code n s mem a used
    rw [eq] at used left
    have right := incomingReply code n s other a used
    exact Option.some.inj (left.symm.trans right)
  · exact agreeOnIncoming code n s mem other

end LiveSegmentReads
