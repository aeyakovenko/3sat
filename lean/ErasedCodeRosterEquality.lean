import Std

namespace ErasedCodeRosterEquality

/-- The read-only computation left after fixing the public query and controller. -/
inductive Tree (Address Word Result : Type) where
  | done (value : Result)
  | probe (address : Address) (next : Word → Tree Address Word Result)

variable {Address Word Result Database Header Choice : Type}

def run (memory : Address → Word) : Tree Address Word Result → Result
  | .done value => value
  | .probe addr next => run memory (next (memory addr))

def transcript (memory : Address → Word) : Tree Address Word Result → List (Address × Word)
  | .done _ => []
  | .probe addr next => (addr, memory addr) :: transcript memory (next (memory addr))

/-- Agreement is required only at the addresses actually observed in the first run. -/
theorem replay (tree : Tree Address Word Result) (a b : Address → Word)
    (agrees : ∀ entry ∈ transcript a tree, b entry.1 = entry.2) :
    run a tree = run b tree := by
  induction tree with
  | done => rfl
  | probe address next ih =>
    have atAddress : b address = a address := agrees (address, a address) (by simp [transcript])
    have afterRead : ∀ entry ∈ transcript a (next (a address)), b entry.1 = entry.2 :=
      fun entry member => agrees entry (List.mem_cons_of_mem _ member)
    simpa only [run, atAddress] using ih (a address) afterRead

theorem authentic (tree : Tree Address Word Result) (a : Address → Word) :
    ∀ entry ∈ transcript a tree, a entry.1 = entry.2 := by
  induction tree with
  | done => simp [transcript]
  | probe address next ih =>
    intro entry member
    rcases List.mem_cons.mp member with equal | tail
    · subst entry
      rfl
    · exact ih (a address) entry tail

/-- The header may encode only the visited set. The query algorithm publicly derives
the tag, basis and canonical input for the corresponding file from that header. -/
def signature (memory : Database → Address → Word) (header : Database → Header)
    (selected : Database → Choice)
    (query : Choice → Header → Database → Tree Address Word Bool)
    (a : Database) : Header × List (Address × Word) :=
  (header a, transcript (memory a) (query (selected a) (header a) a))

/-- A single word transcript identifies the database, although its normalized
sign/program and logical diagonal query need not occur in the signature. -/
theorem identifies (memory : Database → Address → Word) (header : Database → Header)
    (selected : Database → Choice)
    (query : Choice → Header → Database → Tree Address Word Bool)
    (correct : ∀ choice a x, run (memory a) (query choice (header a) x) = true ↔ a = x)
    (a b : Database)
    (equal : signature memory header selected query a = signature memory header selected query b) :
    a = b := by
  have sameHeader : header a = header b := congrArg Prod.fst equal
  have sameTranscript :
      transcript (memory a) (query (selected a) (header a) a) =
      transcript (memory b) (query (selected b) (header b) b) := congrArg Prod.snd equal
  have agrees : ∀ entry ∈ transcript (memory a) (query (selected a) (header a) a),
      memory b entry.1 = entry.2 := by
    rw [sameTranscript]
    exact authentic _ _
  have ra := replay (query (selected a) (header a) a) (memory a) (memory b) agrees
  have accept : run (memory a) (query (selected a) (header a) a) = true :=
    (correct (selected a) a a).mpr rfl
  rw [ra, sameHeader] at accept
  exact ((correct (selected a) b a).mp accept).symm

/-- A public reconstruction of the physical file from a visited set can always
be included in the public query algorithm; it need not be written to the signature. -/
theorem public_reconstruction {Layout : Type} (layout : Header → Layout)
    (memory : Database → Address → Word) (visited : Database → Header)
    (selected : Database → Choice)
    (physical : Choice → Layout → Database → Tree Address Word Bool)
    (correct : ∀ select a x, run (memory a) (physical select (layout (visited a)) x) = true ↔ a = x)
    (a b : Database)
    (equal : signature memory visited selected (fun s v x => physical s (layout v) x) a =
      signature memory visited selected (fun s v x => physical s (layout v) x) b) : a = b :=
  identifies memory visited selected (fun s v x => physical s (layout v) x) correct a b equal

#print axioms replay
#print axioms identifies
#print axioms public_reconstruction

end ErasedCodeRosterEquality
