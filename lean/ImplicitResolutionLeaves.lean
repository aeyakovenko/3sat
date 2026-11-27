import Std

namespace ImplicitResolutionLeaves

structure Literal (n : Nat) where
  name : Fin n
  sign : Bool
  deriving DecidableEq

abbrev Assignment (n : Nat) := Fin n → Bool
abbrev Clause (n : Nat) := List (Literal n)

def blocker {n : Nat} (a : Assignment n) (i : Fin n) : Literal n :=
  ⟨i, !(a i)⟩

def fullLeaf {n : Nat} (a : Assignment n) : Clause n :=
  (List.finRange n).map (blocker a)

/-- Each parent is obtained by resolving its two canonical children on i. -/
def resolvesOn {n : Nat} (i : Fin n) (left right parent : Clause n) : Prop :=
  left = ⟨i, true⟩ :: parent ∧ right = ⟨i, false⟩ :: parent

theorem internal_line {n : Nat} (i : Fin n) (parent : Clause n) :
    resolvesOn i (⟨i, !false⟩ :: parent) (⟨i, !true⟩ :: parent) parent :=
  ⟨rfl, rfl⟩

def selectedAxiom {n : Nat} (p q r : Fin n) (a : Assignment n) (error : Bool) : Clause n :=
  [⟨p, !(xor (a p) error)⟩, blocker a q, blocker a r]

abbrev weakens {n : Nat} (source result : Clause n) : Prop := source ⊆ result

private theorem blocker_in_full {n : Nat} (a : Assignment n) (i : Fin n) :
    blocker a i ∈ fullLeaf a :=
  List.mem_map.mpr ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

private theorem satisfied_not_in_full {n : Nat} (a : Assignment n) (i : Fin n) :
    (⟨i, a i⟩ : Literal n) ∉ fullLeaf a := by
  intro h
  obtain ⟨j, _, eq⟩ := List.mem_map.mp h
  have nm : j = i := congrArg Literal.name eq
  subst j
  have impossible : (!(a i)) = a i := congrArg Literal.sign eq
  cases val : a i <;> simp [val] at impossible

/-- For distinct p,q,r the eight possible selected axioms form the fixed
proper contradiction. This equivalence even permits repeated indices. -/
theorem leaf_valid_iff {n : Nat} (p q r : Fin n) (a : Assignment n) (error : Bool) :
    weakens (selectedAxiom p q r a error) (fullLeaf a) ↔ error = false := by
  cases error with
  | false =>
    simp only [Bool.xor_false, selectedAxiom, weakens, iff_true]
    intro l hl
    rcases (by simpa [blocker] using hl :
      l = blocker a p ∨ l = blocker a q ∨ l = blocker a r) with h | h | h <;>
      subst l <;> exact blocker_in_full _ _
  | true =>
    simp only [Bool.true_eq_false, iff_false]
    intro h
    apply satisfied_not_in_full a p
    apply h
    simp [selectedAxiom]

/-- Counts bad leaves on any enumerated set of assignments.  With a full
enumeration this gives exactly the number of satisfying assignments. -/
theorem failed_lines {n : Nat} (p q r : Fin n) (source : Assignment n → Bool)
    (leaves : List (Assignment n)) :
    leaves.filter (fun a => decide (¬ weakens (selectedAxiom p q r a (source a)) (fullLeaf a))) =
      leaves.filter source := by
  apply List.filter_congr
  intro a _
  cases h : source a <;> simp [leaf_valid_iff]

/-- Only one parent-pointer bit changes.  Entire tables differ at precisely
the assignments where their source predicates differ. -/
theorem changed_pointer_iff (b f g : Bool) :
    xor b f ≠ xor b g ↔ f ≠ g := by
  cases b <;> cases f <;> cases g <;> decide

end ImplicitResolutionLeaves
