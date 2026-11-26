import Std

/-! Finite semantics of placing one query packet at the final fresh aligned
word. The addresses below are packet slots; deterministic work between
loads can be included in the state. -/
namespace LastButterflyWord

def filled {A V : Type} [DecidableEq A] (base : A → V) :
    List (A × V) → A → V
  | [], a => base a
  | (k,v) :: ps, a => if a = k then v else filled base ps a

def distinct {A V : Type} (ps : List (A × V)) : Prop :=
  ps.Pairwise (fun x y => x.1 ≠ y.1)

theorem filled_at {A V : Type} [DecidableEq A] (base : A → V)
    {ps : List (A × V)} (nd : distinct ps) {e : A × V} (mem : e ∈ ps) :
    filled base ps e.1 = e.2 := by
  induction ps with
  | nil => simp at mem
  | cons p ps ih =>
    obtain ⟨fresh, tail⟩ := List.pairwise_cons.mp nd
    rcases List.mem_cons.mp mem with eq | member
    · subst e
      simp [filled]
    · have ne := (fresh e member).symm
      simpa [filled, ne] using ih tail member

def complete {A V : Type} [DecidableEq A] (base : A → V) (ps : List (A × V))
    (last : A) (query : V) (a : A) : V :=
  if a = last then query else filled base ps a

theorem recorded_word {A V : Type} [DecidableEq A] (base : A → V)
    {ps : List (A × V)} {last : A} (q : V) (nd : distinct ps)
    (fresh : ∀ e ∈ ps, e.1 ≠ last) {e : A × V} (he : e ∈ ps) :
    complete base ps last q e.1 = e.2 := by
  simp [complete, fresh e he, filled_at base nd he]

/-- Reading the actual final layout in first-visit order yields the chosen
database records, with exactly the supplied query as the last packet. -/
theorem population {A V : Type} [DecidableEq A] (base : A → V)
    {ps : List (A × V)} {last : A} (q : V) (nd : distinct ps)
    (fresh : ∀ e ∈ ps, e.1 ≠ last) :
    ((ps.map Prod.fst) ++ [last]).map (complete base ps last q) = ps.map Prod.snd ++ [q] := by
  have h : (ps.map Prod.fst).map (complete base ps last q) = ps.map Prod.snd := by
    rw [List.map_map]
    exact List.map_congr_left (fun e he => recorded_word base q nd fresh he)
  simp [List.map_append, h, complete]

/-- Prefixes record repeated loads as well as first visits. -/
inductive Prefix {S A V : Type} (ask : S → A) (move : S → V → S) (mem : A → V) :
    S → List (A × V) → S → Prop
  | nil (s) : Prefix ask move mem s [] s
  | cons {s t tail} (later : Prefix ask move mem (move s (mem (ask s))) tail t) :
      Prefix ask move mem s ((ask s, mem (ask s)) :: tail) t

theorem replay {S A V : Type} {ask : S → A} {move : S → V → S}
    {old : A → V} (other : A → V) {s t : S} {trace : List (A × V)}
    (path : Prefix ask move old s trace t) :
    (∀ e ∈ trace, other e.1 = e.2) → Prefix ask move other s trace t := by
  induction path with
  | nil => exact fun _ => .nil _
  | @cons s t tail later ih =>
    intro agree
    have same : other (ask s) = old (ask s) := agree _ List.mem_cons_self
    have next := ih (fun e he => agree e (List.mem_cons_of_mem _ he))
    have entered : Prefix ask move other (move s (other (ask s))) tail t := by
      simpa only [same] using next
    simpa only [same] using Prefix.cons entered

/-- The next requested address and all earlier physical returns are the
same for *every* supplied query. Neither the query nor its answer was used
to choose the recorded address-to-packet assignments. -/
theorem same_prefix_at_last {S A V : Type} [DecidableEq A]
    {ask : S → A} {move : S → V → S} {old : A → V} (base : A → V)
    {ps trace : List (A × V)} {s t : S} {last : A} (nd : distinct ps)
    (fresh : ∀ e ∈ ps, e.1 ≠ last) (recorded : trace ⊆ ps)
    (path : Prefix ask move old s trace t) (next : ask t = last) (q : V) :
    Prefix ask move (complete base ps last q) s trace t ∧
      complete base ps last q (ask t) = q := by
  exact ⟨replay _ path (fun _ he => recorded_word base q nd fresh (recorded he)),
    by simp [complete, next]⟩

/-- Graph implication clauses pin the source true and target false. -/
inductive Reach {X : Type} (edge : X → X → Prop) (source : X) : X → Prop
  | start : Reach edge source source
  | step {u v} : Reach edge source u → edge u v → Reach edge source v

theorem horn_verdict {X : Type} (edge : X → X → Prop) (s t : X) :
    (∃ p : X → Prop, p s ∧ ¬p t ∧ ∀ u v, edge u v → p u → p v) ↔
      ¬Reach edge s t := by
  constructor
  · rintro ⟨p, source, sink, propagate⟩ path
    have all (v : X) (h : Reach edge s v) : p v := by
      induction h with
      | start => exact source
      | step _ e ih => exact propagate _ _ e ih
    exact sink (all t path)
  · exact fun no => ⟨Reach edge s, .start, no, fun _ _ e path => .step path e⟩

/-- Along the unique possible butterfly path, the doubled-state graph
records whether at least one original edge is absent. -/
theorem missing_flag (edges : List Bool) (initial : Bool) :
    edges.foldl (fun seen present => seen || !present) initial =
      (initial || !(edges.all id)) := by
  induction edges generalizing initial with
  | nil => simp
  | cons e es ih =>
    cases e <;> cases initial <;> simp [ih]

/-- Forcing the queried terminal to false is feasible precisely for the
complementary terminal tag. Thus either of the two verdicts decodes the
original reachability bit. -/
theorem complementary_query (edges : List Bool) (tag : Bool) :
    (edges.foldl (fun seen present => seen || !present) false != tag) =
      (edges.all id == tag) := by
  rw [missing_flag]
  cases edges.all id <;> cases tag <;> rfl

end LastButterflyWord
