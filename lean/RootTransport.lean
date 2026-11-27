import Std

universe u v w

namespace RootTransport

/-- Edges may carry different functions even when their endpoints agree. -/
inductive Path {V : Type u} (Edge : V → V → Type v) : V → V → Type (max u v) where
  | nil (x : V) : Path Edge x x
  | snoc {x y z : V} (p : Path Edge x y) (e : Edge y z) : Path Edge x z

variable {V : Type u} {S : Type w} {Edge : V → V → Type v}
variable (step : ∀ {x y}, Edge x y → S → S)

def transport {x y : V} (p : Path Edge x y) (start : S) : S :=
  match p with
  | .nil _ => start
  | .snoc initial edge => step edge (transport initial start)

def Valid (label : V → S) : Prop :=
  ∀ {x y} (edge : Edge x y), step edge (label x) = label y

theorem agrees_on_path (label : V → S) (valid : Valid (Edge := Edge) step label)
    {x y : V} (p : Path Edge x y) :
    transport step p (label x) = label y := by
  induction p with
  | nil => rfl
  | snoc p edge ih => exact (congrArg (step edge) ih).trans (valid edge)

/-- Two sampled directed paths with common endpoints force equal predictions. -/
theorem agrees_on_comparison (label : V → S) (valid : Valid (Edge := Edge) step label)
    {root target : V} (p q : Path Edge root target) :
    transport step p (label root) = transport step q (label root) :=
  (agrees_on_path step label valid p).trans (agrees_on_path step label valid q).symm

/-- Checking all edges against one chosen root path per vertex characterizes
    the existence of a valid labeling. -/
theorem all_edge_comparisons {root : V} (paths : ∀ x, Path Edge root x) :
    (∃ label : V → S, Valid (Edge := Edge) step label) ↔
    ∃ seed : S, ∀ {x y} (edge : Edge x y),
      step edge (transport step (paths x) seed) = transport step (paths y) seed := by
  constructor
  · rintro ⟨label, valid⟩
    refine ⟨label root, fun {x y} edge => ?_⟩
    exact agrees_on_comparison step label valid (.snoc (paths x) edge) (paths y)
  · rintro ⟨seed, checks⟩
    exact ⟨fun x => transport step (paths x) seed, checks⟩

end RootTransport
