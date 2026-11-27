import Std

namespace PrefixReplyReplay

/-- A memory event after decoding the current register state and proposed replies. -/
inductive Event (Addr Word : Type) where
  | load (addr : Addr) (reply : Word)
  | store (addr : Addr) (value : Word)
  | other

variable {Addr Word : Type} [DecidableEq Addr]

/-- A prefix scan pays attention only to the latest write to the requested cell. -/
def observe (target : Addr) (current : Word) : Event Addr Word → Word
  | .store addr val => if addr = target then val else current
  | _ => current

def latest (initial : Addr → Word) (history : List (Event Addr Word)) (target : Addr) : Word :=
  history.foldl (observe target) (initial target)

def advance (state : Addr → Word) (event : Event Addr Word) (addr : Addr) : Word :=
  observe addr (state addr) event

def agrees (state : Addr → Word) : Event Addr Word → Prop
  | .load addr value => state addr = value
  | _ => True

def legal (state : Addr → Word) : List (Event Addr Word) → Prop
  | [] => True
  | event :: rest => agrees state event ∧ legal (advance state event) rest

def prefixChecks (initial : Addr → Word) (history : List (Event Addr Word)) :
    List (Event Addr Word) → Prop
  | [] => True
  | event :: rest =>
    agrees (latest initial history) event ∧ prefixChecks initial (history ++ [event]) rest

theorem extendHistory (initial : Addr → Word) (history : List (Event Addr Word))
    (event : Event Addr Word) :
    latest initial (history ++ [event]) = advance (latest initial history) event := by
  funext target
  simp [latest, advance, List.foldl_append]

/-- Independent reruns of the speculative prefix check exactly the legal memory traces. -/
theorem prefixChecks_iff_legal (initial : Addr → Word) (history events : List (Event Addr Word)) :
    prefixChecks initial history events ↔ legal (latest initial history) events := by
  induction events generalizing history with
  | nil => rfl
  | cons event rest ih =>
    simp only [prefixChecks, legal, ih, extendHistory]

theorem fromInitial (initial : Addr → Word) (events : List (Event Addr Word)) :
    prefixChecks initial [] events ↔ legal initial events := by
  exact prefixChecks_iff_legal initial [] events

end PrefixReplyReplay
