import Std

/-! Descending through missing true facts in a time-layered Horn proof.
Levels count the initial and final facts, so a path from time t to time
zero has t+1 levels and t edges. -/

namespace HornBackwardWitness

variable {Atom : Type}

/-- A derivation uses initial units at time zero and steps whose premises
are all facts at the preceding time. The body may be empty. -/
inductive Derived (initial : Atom → Prop) (rule : Nat → List Atom → Atom → Prop) :
    Nat → Atom → Prop where
  | init {a} : initial a → Derived initial rule 0 a
  | step {t body head} : rule t body head →
      (∀ a ∈ body, Derived initial rule t a) → Derived initial rule (t+1) head

inductive Violation (initial : Atom → Prop) (rule : Nat → List Atom → Atom → Prop)
    (allow : Nat → Atom → Prop) : Nat → Prop where
  | init {a} : initial a → ¬allow 0 a → Violation initial rule allow 0
  | step {t body head} : rule t body head → (∀ a ∈ body, allow t a) →
      ¬allow (t+1) head → Violation initial rule allow (t+1)

/-- The last two indices are the time of the violated clause and the
number of levels. Every descent follows an actual missing premise. -/
inductive Path (initial : Atom → Prop) (rule : Nat → List Atom → Atom → Prop)
    (allow : Nat → Atom → Prop) : Nat → Atom → Nat → Nat → Prop where
  | init {a} : initial a → ¬allow 0 a → Path initial rule allow 0 a 0 1
  | step {t body head} : rule t body head → (∀ a ∈ body, allow t a) →
      ¬allow (t+1) head → Path initial rule allow (t+1) head (t+1) 1
  | descend {t body head a stop levels} : rule t body head →
      ¬allow (t+1) head → a ∈ body → Derived initial rule t a → ¬allow t a →
      Path initial rule allow t a stop levels →
      Path initial rule allow (t+1) head stop (levels+1)

theorem Path.endpoint {initial : Atom → Prop} {rule : Nat → List Atom → Atom → Prop}
    {allow : Nat → Atom → Prop} {t head stop levels}
    (p : Path initial rule allow t head stop levels) : Violation initial rule allow stop := by
  induction p with
  | init unit missing => exact .init unit missing
  | step fired premises missing => exact .step fired premises missing
  | descend _ _ _ _ _ _ ih => exact ih

theorem missing_has_bounded_path {initial : Atom → Prop}
    {rule : Nat → List Atom → Atom → Prop} {allow : Nat → Atom → Prop} {t head}
    (truth : Derived initial rule t head) (missing : ¬allow t head) :
    ∃ stop levels, Path initial rule allow t head stop levels ∧
      stop + levels = t + 1 ∧ 1 ≤ levels ∧ levels ≤ t + 1 := by
  classical
  induction t generalizing head with
  | zero =>
    cases truth with
    | init unit => exact ⟨0, 1, .init unit missing, by omega, by omega, by omega⟩
  | succ t ih =>
    cases truth with
    | @step _ body _ fired premises =>
      by_cases gap : ∃ a, a ∈ body ∧ ¬allow t a
      · obtain ⟨a, member, absent⟩ := gap
        have truePremise := premises a member
        obtain ⟨stop, n, path, count, pos, bound⟩ := ih truePremise absent
        exact ⟨stop, n+1, .descend fired missing member truePremise absent path,
          by omega, by omega, by omega⟩
      · have visible : ∀ a ∈ body, allow t a := by
          intro a member
          exact Classical.byContradiction (fun absent => gap ⟨a, member, absent⟩)
        exact ⟨t+1, 1, .step fired visible missing, by omega, by omega, by omega⟩

end HornBackwardWitness
