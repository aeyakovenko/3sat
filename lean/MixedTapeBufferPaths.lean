import Std

/-! The plane stores permanent lanes. The line cell for an index is reused by
different source vertices in disjoint transfer intervals. Only faults during
the current interval can break that transfer's buffered leg. -/

namespace MixedTapeBufferPaths

structure Layout (Vertex Index Cell : Type) where
  plane : Nat → Cell
  line : Nat → Index
  owner : Nat → Option Vertex
  decode : Cell → Option (Vertex × Index)
  homeCell : Vertex × Index → Cell
  home : Vertex × Index → Nat
  decode_home : ∀ a, decode (homeCell a) = some a
  visit_home : ∀ a, plane (home a) = homeCell a

variable {V I C : Type} (g : Layout V I C)

/-- Only the source owner, not every user of the current line cell, is charged. -/
def chargesAt (t : Nat) : List (V × I) :=
  (g.decode (g.plane t)).toList ++ ((g.owner t).map (fun v => (v, g.line t))).toList

def charges (faults : List Nat) : List (V × I) := faults.flatMap (chargesAt g)

theorem chargeBudget (faults : List Nat) : (charges g faults).length ≤ 2 * faults.length := by
  have per (t : Nat) : (chargesAt g t).length ≤ 2 := by
    cases h : g.decode (g.plane t) <;> cases k : g.owner t <;> simp [chargesAt, h, k]
  induction faults with
  | nil => simp [charges]
  | cons t ts ih =>
    simp only [charges, List.flatMap_cons, List.length_append, List.length_cons] at *
    have := per t
    omega

def consecutive (pos : Nat → α) (cell : α) (t u : Nat) : Prop :=
  pos t = cell ∧ pos u = cell ∧ t < u ∧ ∀ j, t < j → j < u → pos j ≠ cell

/-- Deletion removes vertices and their incident edges from the original graph. -/
def intactEdge (faults : List Nat) (t u : Nat) : Prop :=
  t ∉ faults ∧ u ∉ faults ∧
    ((∃ c, consecutive g.plane c t u) ∨ (∃ i, consecutive g.line i t u))

/-- The cleanliness hypothesis is local to the closed time interval. -/
private theorem visitChain {pos : Nat → α} {cell : α} {edge : Nat → Nat → Prop}
    (faults : List Nat)
    (step : ∀ t u, t ∉ faults → u ∉ faults → consecutive pos cell t u → edge t u)
    (t u : Nat) (first : pos t = cell) (last : pos u = cell) (ordered : t < u)
    (clean : ∀ j, t ≤ j → j ≤ u → pos j = cell → j ∉ faults) :
    Relation.TransGen edge t u := by
  classical
  by_cases mid : ∃ j, t < j ∧ j < u ∧ pos j = cell
  · obtain ⟨j, htj, hju, hj⟩ := mid
    exact (visitChain faults step t j first hj htj
      (fun k h₁ h₂ => clean k h₁ (by omega))).trans
      (visitChain faults step j u hj last hju (fun k h₁ h₂ => clean k (by omega) h₂))
  · exact .single (step t u (clean t (by omega) (by omega) first)
      (clean u (by omega) (by omega) last)
      ⟨first, last, ordered, fun j htj hju hj => mid ⟨j, htj, hju, hj⟩⟩)
termination_by u - t
decreasing_by all_goals omega

/-- A load and drain for one lifted edge of one transfer pass. The line index
is the source index on both visits, even when the target has a different index. -/
structure Transfer (src dst : V × I) where
  load : Nat
  drain : Nat
  before_load : g.home src < load
  before_drain : load < drain
  before_target : drain < g.home dst
  load_plane : g.plane load = g.homeCell src
  load_line : g.line load = src.2
  drain_line : g.line drain = src.2
  drain_plane : g.plane drain = g.homeCell dst
  active : ∀ j, load ≤ j → j ≤ drain → g.owner j = some src.1

private theorem planeClean (faults : List Nat) {a : V × I}
    (unmarked : a ∉ charges g faults) {t : Nat} (visit : g.plane t = g.homeCell a) :
    t ∉ faults := by
  intro fault
  apply unmarked
  exact List.mem_flatMap.mpr ⟨t, fault, List.mem_append_left _
    (by simp [visit, g.decode_home])⟩

private theorem lineClean (faults : List Nat) {a : V × I}
    (unmarked : a ∉ charges g faults) {t : Nat}
    (active : g.owner t = some a.1) (visit : g.line t = a.2) : t ∉ faults := by
  intro fault
  apply unmarked
  exact List.mem_flatMap.mpr ⟨t, fault, List.mem_append_right _
    (by simp [active, visit])⟩

/-- All three chains consist of original consecutive-visit edges. An earlier
or later fault at the same line cell under another owner is permitted. -/
theorem liftTransfer (faults : List Nat) {src dst : V × I}
    (x : Transfer g src dst) (hs : src ∉ charges g faults) (hd : dst ∉ charges g faults) :
    Relation.TransGen (intactEdge g faults) (g.home src) (g.home dst) := by
  have planeStep (c : C) (t u : Nat) (ht : t ∉ faults) (hu : u ∉ faults)
      (e : consecutive g.plane c t u) : intactEdge g faults t u :=
    ⟨ht, hu, Or.inl ⟨c, e⟩⟩
  have lineStep (i : I) (t u : Nat) (ht : t ∉ faults) (hu : u ∉ faults)
      (e : consecutive g.line i t u) : intactEdge g faults t u :=
    ⟨ht, hu, Or.inr ⟨i, e⟩⟩
  have first := visitChain faults (planeStep (g.homeCell src)) (g.home src) x.load
    (g.visit_home src) x.load_plane x.before_load (fun _ _ _ h => planeClean g faults hs h)
  have middle := visitChain faults (lineStep src.2) x.load x.drain
    x.load_line x.drain_line x.before_drain (fun j hj hk h =>
      lineClean g faults hs (x.active j hj hk) h)
  have last := visitChain faults (planeStep (g.homeCell dst)) x.drain (g.home dst)
    x.drain_plane (g.visit_home dst) x.before_target (fun _ _ _ h => planeClean g faults hd h)
  exact (first.trans middle).trans last

/-- A single list of length at most twice the fault count protects every path
whose lanes avoid the list. The list bound includes repeated charges. -/
theorem faultTolerantLift (faults : List Nat) :
    ∃ bad : List (V × I), bad.length ≤ 2 * faults.length ∧
      ∀ src dst, Relation.TransGen
        (fun a b => Nonempty (Transfer g a b) ∧ a ∉ bad ∧ b ∉ bad) src dst →
        Relation.TransGen (intactEdge g faults) (g.home src) (g.home dst) := by
  refine ⟨charges g faults, chargeBudget g faults, ?_⟩
  intro src dst path
  induction path with
  | single edge =>
    obtain ⟨⟨x⟩, hs, hd⟩ := edge
    exact liftTransfer g faults x hs hd
  | tail _ edge ih =>
    obtain ⟨⟨x⟩, hs, hd⟩ := edge
    exact ih.trans (liftTransfer g faults x hs hd)

end MixedTapeBufferPaths
