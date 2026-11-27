import Std

namespace BooleanTreeRelay

inductive Tree (Site Index : Type) where
  | leaf (x : Site)
  | node (x : Site) (children : Index → Tree Site Index)

def root : Tree Site Index → Site
  | .leaf x => x
  | .node x _ => x

def evaluate (gate : (Index → Bool) → Bool) (leaf : Site → Bool) :
    Tree Site Index → Bool
  | .leaf x => leaf x
  | .node _ children => gate (fun j => evaluate gate leaf (children j))

def copies (query : Site → Bool) (components : Site → Index → Bool) :
    Tree Site Index → Prop
  | .leaf _ => True
  | .node x children => (∀ j, query (root (children j)) = components x j) ∧
      ∀ j, copies query components (children j)

theorem relay (gate : (Index → Bool) → Bool) (components : Site → Index → Bool)
    (query : Site → Bool) (uses : ∀ x, query x = gate (components x))
    (sites : Tree Site Index) (joined : copies query components sites) :
    evaluate gate query sites = query (root sites) := by
  induction sites with
  | leaf x => rfl
  | node x children ih =>
    obtain ⟨atChild, deeper⟩ := joined
    simp only [evaluate, root, uses x]
    congr 1
    funext j
    exact (ih j (deeper j)).trans (atChild j)

theorem endpoint_opposite (gate : (Index → Bool) → Bool) (components : Site → Index → Bool)
    (query : Site → Bool) (uses : ∀ x, query x = gate (components x))
    (sites : Tree Site Index) (joined : copies query components sites) :
    (!evaluate gate query sites) ≠ query (root sites) := by
  rw [relay gate components query uses sites joined]
  cases query (root sites) <;> decide

theorem one_patch (pristine present repaired : Bool) (witnessed : repaired = true → present = true) :
    (repaired || (pristine && !present)) = (if present then repaired else pristine) := by
  cases pristine <;> cases present <;> cases repaired <;> simp_all

end BooleanTreeRelay
