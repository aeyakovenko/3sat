import Std

namespace PartitionWitness

variable {Choice Code : Type}

/-- One shared description is supplied before each challenge selects a child. -/
def game : Nat → (List Choice → List Code → Prop) → Prop
  | 0, legal => legal [] []
  | n+1, legal => ∃ a, ∀ c, game n (fun cs xs => legal (c::cs) (a::xs))

/-- Read the public node descriptions addressed by a root-to-leaf path. -/
def pathCodes (table : List Choice → Code) : List Choice → List Code
  | [] => []
  | c::cs => table [] :: pathCodes (fun p => table (c::p)) cs

/-- Separate existential choices in disjoint subtrees glue to one consistent
    labeling of the entire tree. Every challenge consults that same labeling. -/
theorem global_table [Inhabited Code] (h : Nat)
    (legal : List Choice → List Code → Prop) :
    game h legal ↔ ∃ table : List Choice → Code,
      ∀ path : List Choice, path.length = h → legal path (pathCodes table path) := by
  classical
  induction h generalizing legal with
  | zero =>
    constructor
    · intro ok
      refine ⟨fun _ => default, ?_⟩
      intro p hp
      cases p with
      | nil => exact ok
      | cons _ _ => simp at hp
    · rintro ⟨table, ok⟩
      exact ok [] rfl
  | succ h ih =>
    constructor
    · rintro ⟨a, next⟩
      have children := fun c => (ih _).mp (next c)
      let table : List Choice → Code
        | [] => a
        | c::p => Classical.choose (children c) p
      refine ⟨table, ?_⟩
      intro p hp
      cases p with
      | nil => simp at hp
      | cons c cs =>
        have hv : cs.length = h := by simpa using hp
        exact Classical.choose_spec (children c) cs hv
    · rintro ⟨table, ok⟩
      refine ⟨table [], fun c => (ih _).mpr ?_⟩
      refine ⟨fun p => table (c::p), ?_⟩
      intro cs hlen
      exact ok (c::cs) (by simp [hlen])

end PartitionWitness
