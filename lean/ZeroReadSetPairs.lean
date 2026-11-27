import Std

namespace ZeroReadSetPairs

/-- Nodes expose only an incoming word that the suffix still needs from
the cut. Local stores and computations are included in the continuation. -/
inductive Query (α : Type) where
  | halt (answer : Bool)
  | read (address : α) (next : Nat → Query α)

def answer (q : Query α) (mem : α → Nat) : Bool :=
  match q with
  | .halt v => v
  | .read a next => answer (next (mem a)) mem

def probes (q : Query α) (mem : α → Nat) : List α :=
  match q with
  | .halt _ => []
  | .read a next => a :: probes (next (mem a)) mem

theorem agreeing_run (q : Query α) (mem other : α → Nat)
    (agree : ∀ a ∈ probes q mem, mem a = other a) :
    answer q mem = answer q other := by
  induction q with
  | halt v => rfl
  | read a next ih =>
    have atHead := agree a (List.mem_cons_self)
    simp only [answer]
    rw [← atHead]
    apply ih
    intro b hb
    exact agree b (List.mem_cons_of_mem _ hb)

theorem unexpected_positive (q : Query α) (ref mem other : α → Nat)
    (keep : ∀ a ∈ probes q mem, mem a ≠ ref a → other a = mem a)
    (different : answer q mem ≠ answer q other) :
    ∃ a ∈ probes q mem, mem a = ref a ∧ other a ≠ ref a := by
  classical
  apply Classical.byContradiction
  intro missing
  apply different
  apply agreeing_run
  intro a ha
  by_cases h : mem a = ref a
  · by_cases t : other a = ref a
    · exact h.trans t.symm
    · exact False.elim (missing ⟨a,ha,h,t⟩)
  · exact (keep a ha h).symm

def separates (rank : α → Nat) (marks tests : α → Prop) : Prop :=
  ∀ a b, marks a → tests b → rank a < rank b

theorem exclusive_orders (rank : α → Nat) (marks tests marks' tests' : α → Prop)
    (h₁ : ∃ a, marks a ∧ tests' a)
    (h₂ : ∃ b, marks' b ∧ tests b) :
    ¬ (separates rank marks tests ∧ separates rank marks' tests') := by
  rintro ⟨s,t⟩
  obtain ⟨a,ha,ha'⟩ := h₁
  obtain ⟨b,hb',hb⟩ := h₂
  exact Nat.lt_asymm (s a b ha hb) (t b a hb' ha')

end ZeroReadSetPairs
