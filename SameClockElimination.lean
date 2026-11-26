import Std

namespace SameClockElimination

/-- A presentation can carry a physical file and any promised public metadata.
The mask is explicit so no consistency between trials on different masks is assumed. -/
structure Trials (Code File : Type) where
  file : Nat → List Code → File
  winner : Nat → List Code → Option Code
  positive : File → Prop
  timelyYes : Nat → List Code → Code → File → Prop

variable {Code File : Type} [DecidableEq Code]

/-- These are the semantic obligations of the bounded compiler and its driver. -/
structure Faithful (T : Trials Code File) (clock : Nat) : Prop where
  hit : ∀ active p, T.winner clock active = some p →
    p ∈ active ∧ T.timelyYes clock active p (T.file clock active) ∧
      ¬ T.positive (T.file clock active)
  quiet : ∀ active, T.winner clock active = none →
    T.positive (T.file clock active) ∧
      ∀ p ∈ active, ¬ T.timelyYes clock active p (T.file clock active)

/-- Each log entry records the actual mask and its first observed YES. -/
inductive Run (T : Trials Code File) (clock : Nat) :
    List Code → List (List Code × Code) → List Code → Prop where
  | stop {active} (quiet : T.winner clock active = none) :
      Run T clock active [] active
  | remove {active p log terminal} (hit : T.winner clock active = some p)
      (rest : Run T clock (active.erase p) log terminal) :
      Run T clock active ((active, p) :: log) terminal

private theorem terminates (T : Trials Code File) (clock : Nat)
    (faithful : Faithful T clock) (initial : List Code) :
    ∃ log terminal, Run T clock initial log terminal := by
  suffices build : ∀ n (active : List Code), active.length = n →
      ∃ log terminal, Run T clock active log terminal from
    build initial.length initial rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro active length_eq
    cases answer : T.winner clock active with
    | none => exact ⟨[], active, .stop answer⟩
    | some p =>
      have member := (faithful.hit active p answer).1
      have positive_length := List.length_pos_of_mem member
      have smaller : (active.erase p).length < n := by
        rw [List.length_erase_of_mem member, length_eq]
        omega
      obtain ⟨log, terminal, rest⟩ := ih _ smaller (active.erase p) rfl
      exact ⟨(active, p) :: log, terminal, .remove answer rest⟩

/-- A verifier of the log can reconstruct each removed candidate's negative input.
The initial pool may even contain duplicate codes. -/
structure Certificate (T : Trials Code File) (clock : Nat) (initial : List Code)
    (log : List (List Code × Code)) (terminal : List Code) : Prop where
  count : log.length + terminal.length = initial.length
  removed : ∀ entry ∈ log, entry.2 ∈ entry.1 ∧
    T.timelyYes clock entry.1 entry.2 (T.file clock entry.1) ∧
      ¬ T.positive (T.file clock entry.1)
  positive : T.positive (T.file clock terminal)
  noYes : ∀ p ∈ terminal, ¬ T.timelyYes clock terminal p (T.file clock terminal)
  cover : ∀ p ∈ initial, p ∈ terminal ∨ ∃ active, (active, p) ∈ log
  subset : ∀ p ∈ terminal, p ∈ initial

private theorem certify {T : Trials Code File} {clock : Nat}
    (faithful : Faithful T clock) {initial log terminal}
    (run : Run T clock initial log terminal) : Certificate T clock initial log terminal := by
  induction run with
  | stop quiet =>
    have result := faithful.quiet _ quiet
    exact ⟨by simp, by simp, result.1, result.2,
      fun _ member => Or.inl member, fun _ member => member⟩
  | @remove active p log terminal hit _ ih =>
    have failure := faithful.hit active p hit
    have positive_length := List.length_pos_of_mem failure.1
    have erase_length := List.length_erase_of_mem failure.1
    refine ⟨?_, ?_, ih.positive, ih.noYes, ?_, ?_⟩
    · have count := ih.count
      simp only [List.length_cons]
      omega
    · intro entry member
      rcases List.mem_cons.mp member with same | later
      · subst entry
        exact failure
      · exact ih.removed entry later
    · intro q member
      by_cases same : q = p
      · subst q
        exact Or.inr ⟨active, List.mem_cons_self⟩
      · have stays := (List.mem_erase_of_ne same).mpr member
        rcases ih.cover q stays with final_member | ⟨a, found⟩
        · exact Or.inl final_member
        · exact Or.inr ⟨a, List.mem_cons_of_mem _ found⟩
    · intro q member
      exact List.mem_of_mem_erase (ih.subset q member)

/-- Positive soundness is only needed on the actual presentations from this clock. -/
def SoundAt (T : Trials Code File) (clock : Nat) (p : Code) : Prop :=
  ∀ active, p ∈ active → T.timelyYes clock active p (T.file clock active) →
    T.positive (T.file clock active)

/-- At most one more trial than initial entries. Every sound candidate from the
initial pool survives and gives no timely YES on the very same positive presentation. -/
theorem same_clock_exhaustion (T : Trials Code File) (clock : Nat)
    (faithful : Faithful T clock) (initial : List Code) :
    ∃ log terminal, Run T clock initial log terminal ∧
      Certificate T clock initial log terminal ∧
      log.length + 1 ≤ initial.length + 1 ∧
      ∀ p ∈ initial, SoundAt T clock p →
        p ∈ terminal ∧ ¬ T.timelyYes clock terminal p (T.file clock terminal) := by
  obtain ⟨log, terminal, run⟩ := terminates T clock faithful initial
  have cert := certify faithful run
  refine ⟨log, terminal, run, cert, ?_, ?_⟩
  · have count := cert.count
    omega
  · intro p member sound
    rcases cert.cover p member with survives | ⟨active, found⟩
    · exact ⟨survives, cert.noYes p survives⟩
    · have failure := cert.removed (active, p) found
      exact False.elim (failure.2.2 (sound active failure.1 failure.2.1))

end SameClockElimination
