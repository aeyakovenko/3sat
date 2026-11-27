import Std

/-! Each site checks one clause of the same formula using one shared bit
assignment. A model certifies the joint assertion that some site is quiet.
This file checks the logic at one block size. Compilation of the proof
verifier, coherence of the actual calls and native timing are external. -/

namespace JointProofClauseSites

variable {Site Atom : Type}

abbrev Assignment (Atom : Type) := Atom → Bool
abbrev Clause (Atom : Type) := List (Atom × Bool)

def Holds (c : Clause Atom) (a : Assignment Atom) : Prop :=
  ∃ i b, (i, b) ∈ c ∧ a i = b

def Model (clauses : Site → Clause Atom) (a : Assignment Atom) : Prop :=
  ∀ z, Holds (clauses z) a

/-- A local latch need only imply its own clause. If all sites latch, the
same assignment gives a model, so no identification of a quiet site from
an individual satisfying assignment is used by the program. -/
theorem some_quiet (clauses : Site → Clause Atom) (read : Assignment Atom)
    (latched : Site → Prop)
    (localCheck : ∀ z, latched z → Holds (clauses z) read)
    (sound : (∃ a, Model clauses a) → ∃ z, ¬latched z) :
    ∃ z, ¬latched z := by
  classical
  by_cases all : ∀ z, latched z
  · exact sound ⟨read, fun z => localCheck z (all z)⟩
  · exact Classical.not_forall.mp all

/-- A decoder may use any coherent model-selection rule. Correctness when
models exist plus completion of passing sites forces absence of a model. -/
theorem no_model_of_coherent_choice (clauses : Site → Clause Atom)
    (read : Assignment Atom) (latched : Site → Prop)
    (localCheck : ∀ z, latched z → Holds (clauses z) read)
    (sound : (∃ a, Model clauses a) → ∃ z, ¬latched z)
    (selects : (∃ a, Model clauses a) → Model clauses read)
    (timely : ∀ z, Holds (clauses z) read → latched z) :
    ¬∃ a, Model clauses a := by
  intro existsModel
  obtain ⟨z, quiet⟩ := some_quiet clauses read latched localCheck sound
  exact quiet (timely z (selects existsModel z))

/-- An ordinary existential bit query recovers a common assignment when
its preferred family contains exactly one member. -/
theorem unique_choice_bits {preferred : Assignment Atom → Prop}
    {winner read : Assignment Atom}
    (existsWinner : preferred winner)
    (unique : ∀ a, preferred a → a = winner)
    (answer : ∀ i, read i = true ↔ ∃ a, preferred a ∧ a i = true) :
    read = winner := by
  funext i
  cases hw : winner i with
  | false =>
    cases hr : read i with
    | false => rfl
    | true =>
      obtain ⟨a, ha, bit⟩ := (answer i).1 hr
      rw [unique a ha, hw] at bit
      contradiction
  | true => exact (answer i).2 ⟨winner, existsWinner, hw⟩

/-! In the prefix-tree variant each node has remaining depth and a prefix
stored in reverse order. This encoding permits a site per full prefix.
Variables below do not assume an algorithm for deciding extension. -/

def HasExtension (accepts : List Bool → Prop) : Nat → List Bool → Prop
  | 0, p => accepts p
  | n+1, p => HasExtension accepts n (false :: p) ∨ HasExtension accepts n (true :: p)

def TreeChecks (accepts : List Bool → Prop) (dead : Nat → List Bool → Prop) :
    Nat → List Bool → Prop
  | 0, p => ¬accepts p → dead 0 p
  | n+1, p =>
    (dead n (false :: p) → dead n (true :: p) → dead (n+1) p) ∧
    TreeChecks accepts dead n (false :: p) ∧ TreeChecks accepts dead n (true :: p)

/-- All checked nodes and a live root entail an accepting leaf at the
required depth, even when the supplied dead labels are arbitrary. -/
theorem live_has_extension {accepts : List Bool → Prop} {dead : Nat → List Bool → Prop}
    {n p} (checks : TreeChecks accepts dead n p) (live : ¬dead n p) :
    HasExtension accepts n p := by
  classical
  induction n generalizing p with
  | zero => exact Classical.byContradiction (fun reject => live (checks reject))
  | succ n ih =>
    obtain ⟨branch, left, right⟩ := checks
    by_cases dl : dead n (false :: p)
    · exact Or.inr (ih right (fun dr => live (branch dl dr)))
    · exact Or.inl (ih left dl)

/-- Exact negative extension answers satisfy every node's local rule. -/
theorem honest_tree (accepts : List Bool → Prop) (n : Nat) (p : List Bool) :
    TreeChecks accepts (fun depth bits => ¬HasExtension accepts depth bits) n p := by
  induction n generalizing p with
  | zero => exact fun reject => reject
  | succ n ih =>
    exact ⟨(fun left right child => child.elim left right), ih _, ih _⟩

end JointProofClauseSites
