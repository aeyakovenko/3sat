import Std

namespace SmallerRejectionTest

/-- Chronological stores are kept newest first. Their array indices in the physical
verifier are time stamps. This predicate names the first matching entry. -/
structure Store (Addr Word : Type) where
  stamp : Nat
  addr : Addr
  value : Word

def latest {A W : Type} [DecidableEq A] (a : A) :
    List (Store A W) → Option (Nat × W)
  | [] => none
  | s :: tail => if s.addr = a then some (s.stamp, s.value) else latest a tail

inductive Witness {A W : Type} (a : A) :
    List (Store A W) → Option (Nat × W) → Prop
  | init : Witness a [] none
  | hit (s : Store A W) (tail) (matchAddr : s.addr = a) :
      Witness a (s :: tail) (some (s.stamp,s.value))
  | skip (s : Store A W) (miss : s.addr ≠ a) {tail result} :
      Witness a tail result → Witness a (s :: tail) result

theorem witness_iff {A W : Type} [DecidableEq A] (a : A)
    (history : List (Store A W)) (result : Option (Nat × W)) :
    Witness a history result ↔ latest a history = result := by
  constructor
  · intro named
    induction named with
    | init => rfl
    | hit s tail ha => simp [latest, ha]
    | skip s ha h ih => simpa [latest, ha] using ih
  · intro h
    subst result
    induction history with
    | nil => exact .init
    | cons s tail ih =>
      by_cases hit : s.addr = a
      · simpa [latest,hit] using Witness.hit (a := a) s tail hit
      · simpa [latest,hit] using Witness.skip s hit ih

section Files

variable {I D : Type} (outer : Prop) (inner : I → D → Prop)
    (history : I → D → Prop) (largeNo : I → Prop) (smallNo : I → I → D → Prop)

/-- The local equivalence is semantic: an unsatisfiable defect file certifies a
real bounded return, even when the program making the return is dishonest. -/
theorem expose_on_positive
    (valid : ∀ i d, (¬ inner i d) ↔ history i d)
    (actual : ∀ i d, history i d → largeNo i)
    (compilation : outer ↔ ∃ i d j, smallNo j i d)
    (positive : outer) :
    (∃ i, largeNo i ∧ outer) ∨
      ∃ j i d, smallNo j i d ∧ inner i d := by
  obtain ⟨i,d,j,reply⟩ := compilation.mp positive
  by_cases neg : largeNo i
  · exact Or.inl ⟨i,neg,positive⟩
  · right
    refine ⟨j,i,d,reply,?_⟩
    exact Classical.byContradiction fun absent => neg (actual i d ((valid i d).mp absent))

theorem unsat_of_sound
    (valid : ∀ i d, (¬ inner i d) ↔ history i d)
    (actual : ∀ i d, history i d → largeNo i)
    (compilation : outer ↔ ∃ i d j, smallNo j i d)
    (largeSound : ∀ i, largeNo i → ¬outer)
    (smallSound : ∀ j i d, smallNo j i d → ¬inner i d) : ¬outer := by
  intro hp
  rcases expose_on_positive outer inner history largeNo smallNo valid actual compilation hp
    with ⟨i, bad, truth⟩ | ⟨j,i,d,bad,truth⟩
  · exact largeSound i bad truth
  · exact smallSound j i d bad truth

theorem smaller_common_miss
    (valid : ∀ i d, (¬ inner i d) ↔ history i d)
    (compilation : outer ↔ ∃ i d j, smallNo j i d)
    (negative : ¬outer) {i d} (described : history i d) :
    (¬inner i d) ∧ ∀ j, ¬smallNo j i d := by
  exact ⟨(valid i d).mpr described, fun j vote => negative (compilation.mpr ⟨i,d,j,vote⟩)⟩

end Files

/-- Each positive trial has a removable false reporter. A terminal sublist
contains every honest reporter from the original list. -/
theorem terminal {I : Type} [DecidableEq I] (pos : List I → Prop) (honest : I → Prop)
    (remove : ∀ s, pos s → ∃ i ∈ s, ¬ honest i) (s : List I) :
    ∃ t, t.Sublist s ∧ ¬pos t ∧ ∀ i ∈ s, honest i → i ∈ t := by
  by_cases hp : pos s
  · obtain ⟨j,mem,bad⟩ := remove s hp
    obtain ⟨t,sub,stop,keep⟩ := terminal pos honest remove (s.erase j)
    refine ⟨t, sub.trans List.erase_sublist, stop, ?_⟩
    intro i hi good
    have ne : i ≠ j := fun eq => bad (eq ▸ good)
    exact keep i ((List.mem_erase_of_ne ne).mpr hi) good
  · exact ⟨s, List.Sublist.refl _, hp, fun _ hi _ => hi⟩
termination_by s.length
decreasing_by
  have hn : 0 < s.length := List.length_pos_of_mem mem
  rw [List.length_erase_of_mem mem]
  omega

/-- Distinct representatives, in reverse chronological rank order. -/
inductive Prefix {I : Type} (edge : Nat → I → Prop) : Nat → List I → Prop
  | empty : Prefix edge 0 []
  | push {n used i} : Prefix edge n used → i ∉ used → edge n i →
      Prefix edge (n+1) (i :: used)

theorem edge_of_used {I : Type} {edge : Nat → I → Prop} {n used}
    (matching : Prefix edge n used) {i} (hi : i ∈ used) :
    ∃ s < n, edge s i := by
  induction matching with
  | empty => simp at hi
  | @push n used j prior fresh linked ih =>
    rcases List.mem_cons.mp hi with rfl | older
    · exact ⟨n, by omega, linked⟩
    · obtain ⟨s,lt,h⟩ := ih older
      exact ⟨s, by omega, h⟩

theorem no_terminal_edge {I : Type} {edge : Nat → I → Prop} {r used}
    (before : Prefix edge r used) (stop : ¬∃ next, Prefix edge (r+1) next)
    (i : I) (earlier : ∀ s < r, ¬edge s i) : ¬edge r i := by
  intro h
  have fresh : i ∉ used := by
    intro mem
    obtain ⟨s,lt,ed⟩ := edge_of_used before mem
    exact earlier s lt ed
  exact stop ⟨i :: used, .push before fresh h⟩

/-- Coverage on canonical replays alone excludes these rank predictions. No
runtime or correctness condition on other queries occurs in this statement. -/
theorem replay_excludes_prediction {I : Type} {edge : Nat → I → Prop}
    {r used} (before : Prefix edge r used)
    (stop : ¬∃ next, Prefix edge (r+1) next)
    (forecastRank : I → Nat) (short : I → Prop)
    (dedicated : ∀ i s, edge s i → forecastRank i = s)
    (replayed : ∀ i, short i → edge (forecastRank i) i) (i : I) (fast : short i) :
    forecastRank i ≠ r := by
  intro hit
  apply no_terminal_edge before stop i (fun s lt e => by
    have earlier := dedicated i s e
    omega)
  simpa [hit] using replayed i fast

end SmallerRejectionTest
