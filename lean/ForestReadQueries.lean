import Std

namespace ForestReadQueries

abbrev Edge (V : Type) := V × V

def graphRead (x : V → Bool) : List (Edge V) → Bool
  | [] => false
  | (u,v) :: rest => (x u && x v) || graphRead x rest

def pin [DecidableEq V] (a b : V) (s t : Bool) (v : V) : Bool :=
  if v = a then s else if v = b then t else false

def edgeMatches [DecidableEq V] (a b u v : V) : Bool :=
  if u = a then decide (v = b) else if u = b then decide (v = a) else false

def adjacent [DecidableEq V] (a b : V) : List (Edge V) → Bool
  | [] => false
  | (u,v) :: rest => edgeMatches a b u v || adjacent a b rest

def Loopless : List (Edge V) → Prop
  | [] => True
  | (u,v) :: rest => u ≠ v ∧ Loopless rest

private theorem pinTerm [DecidableEq V] (a b u v : V) (distinct : a ≠ b)
    (loopless : u ≠ v) (s t : Bool) :
    (pin a b s t u && pin a b s t v) = (edgeMatches a b u v && s && t) := by
  have reverse : b ≠ a := Ne.symm distinct
  by_cases hua : u = a <;> by_cases hub : u = b <;>
    by_cases hva : v = a <;> by_cases hvb : v = b <;>
    first
    | exact False.elim (distinct (hua.symm.trans hub))
    | exact False.elim (distinct (hva.symm.trans hvb))
    | exact False.elim (loopless (hua.trans hva.symm))
    | exact False.elim (loopless (hub.trans hvb.symm))
    | cases s <;> cases t <;>
      simp (disch := assumption) only [pin, edgeMatches, if_pos, if_neg, decide_eq_true, decide_eq_false] <;> rfl

/-- Pin all vertices except two to zero, for any finite loopless edge list.
    Reversing or repeating an edge in the list causes no problem. -/
theorem twoFree [DecidableEq V] (a b : V) (distinct : a ≠ b)
    (s t : Bool) (edges : List (Edge V)) (simple : Loopless edges) :
    graphRead (pin a b s t) edges = (adjacent a b edges && s && t) := by
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv,hrest⟩ := simple
    change ((pin a b s t u && pin a b s t v) || graphRead (pin a b s t) rest) = _
    rw [pinTerm a b u v distinct huv, ih hrest]
    change _ = ((edgeMatches a b u v || adjacent a b rest) && s && t)
    cases edgeMatches a b u v <;> cases adjacent a b rest <;> cases s <;> cases t <;> rfl

def IsAffine (f : Bool → Bool → Bool) : Prop :=
  ∃ c p q : Bool, ∀ s t, f s t = (c ^^ (p && s) ^^ (q && t))

def IsZero (f : Bool → Bool → Bool) : Prop := ∀ s t, f s t = false

theorem andNotAffine : ¬ IsAffine (fun s t => s && t) := by
  rintro ⟨c,p,q,h⟩
  have h00 := h false false
  have h10 := h true false
  have h01 := h false true
  have h11 := h true true
  cases c <;> cases p <;> cases q <;> contradiction

theorem affineIffMissing [DecidableEq V] (a b : V) (distinct : a ≠ b)
    (edges : List (Edge V)) (simple : Loopless edges) :
    IsAffine (fun s t => graphRead (pin a b s t) edges) ↔ adjacent a b edges = false := by
  constructor
  · rintro ⟨c,p,q,h⟩
    cases he : adjacent a b edges with
    | false => rfl
    | true =>
      apply False.elim
      apply andNotAffine
      refine ⟨c,p,q,?_⟩
      intro s t
      have eq := h s t
      change graphRead (pin a b s t) edges = _ at eq
      rw [twoFree a b distinct s t edges simple, he] at eq
      exact eq
  · intro he
    refine ⟨false,false,false,?_⟩
    intro s t
    change graphRead (pin a b s t) edges = _
    rw [twoFree a b distinct s t edges simple, he]
    rfl

theorem zeroIffMissing [DecidableEq V] (a b : V) (distinct : a ≠ b)
    (edges : List (Edge V)) (simple : Loopless edges) :
    IsZero (fun s t => graphRead (pin a b s t) edges) ↔ adjacent a b edges = false := by
  constructor
  · intro h
    have eq := h true true
    change graphRead (pin a b true true) edges = false at eq
    rw [twoFree a b distinct true true edges simple] at eq
    cases he : adjacent a b edges <;> rw [he] at eq <;> exact eq
  · intro he s t
    change graphRead (pin a b s t) edges = _
    rw [twoFree a b distinct s t edges simple, he]
    rfl

abbrev Vertex := Sum Nat Nat

/-- One column per successive row. A permutation column list represents its
    bipartite perfect matching; the proof also covers repeated columns. -/
def rowEdges : Nat → List Nat → List (Edge Vertex)
  | _, [] => []
  | start, col :: tail => (.inl start, .inr col) :: rowEdges (start+1) tail

private theorem rowsLoopless (cols : List Nat) (start : Nat) : Loopless (rowEdges start cols) := by
  induction cols generalizing start with
  | nil => trivial
  | cons col tail ih => exact ⟨Sum.noConfusion, ih (start+1)⟩

private theorem rowMatch (i col start first : Nat) :
    edgeMatches (.inl i : Vertex) (.inr col) (.inl start) (.inr first) =
      (if start = i then decide (first = col) else false) := by
  unfold edgeMatches
  by_cases hr : start = i
  · cases hr
    rw [if_pos rfl, if_pos rfl]
    by_cases hc : first = col
    · cases hc
      rw [decide_eq_true rfl, decide_eq_true rfl]
    · rw [decide_eq_false (fun h => hc (Sum.inr.inj h)), decide_eq_false hc]
  · rw [if_neg (fun h => hr (Sum.inl.inj h)), if_neg (fun h => Sum.noConfusion h), if_neg hr]

private theorem noEarlyRow (cols : List Nat) (start i col : Nat) (before : i < start) :
    adjacent (.inl i : Vertex) (.inr col) (rowEdges start cols) = false := by
  induction cols generalizing start with
  | nil => rfl
  | cons first tail ih =>
    have ne : start ≠ i := Nat.ne_of_gt before
    have noTail := ih (start+1) (Nat.lt_succ_of_lt before)
    change (edgeMatches (.inl i : Vertex) (.inr col) (.inl start) (.inr first) || _) = _
    rw [rowMatch, if_neg ne, noTail]
    rfl

def rowLookup : List Nat → Nat → Option Nat
  | [], _ => none
  | col :: _, 0 => some col
  | _ :: tail, i+1 => rowLookup tail i

private theorem incidence (cols : List Nat) (start i col : Nat) :
    adjacent (.inl (start+i) : Vertex) (.inr col) (rowEdges start cols) =
    decide (rowLookup cols i = some col) := by
  induction cols generalizing start i with
  | nil => rfl
  | cons first tail ih =>
    cases i with
    | zero =>
      have noTail := noEarlyRow tail (start+1) start col (Nat.lt_succ_self start)
      change (edgeMatches (.inl start : Vertex) (.inr col) (.inl start) (.inr first) ||
        adjacent (.inl start : Vertex) (.inr col) (rowEdges (start+1) tail)) =
        decide ((some first : Option Nat) = some col)
      rw [rowMatch, if_pos rfl, noTail, Bool.or_false]
      by_cases eq : first = col
      · cases eq
        rw [decide_eq_true rfl, decide_eq_true rfl]
      · rw [decide_eq_false eq, decide_eq_false (fun h => eq (Option.some.inj h))]
    | succ i =>
      have ne : start ≠ start+(i+1) := Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.zero_lt_succ i))
      have same : start+(i+1) = (start+1)+i := (Nat.add_succ start i).trans (Nat.succ_add start i).symm
      change (edgeMatches (.inl (start+(i+1)) : Vertex) (.inr col) (.inl start) (.inr first) ||
        adjacent (.inl (start+(i+1)) : Vertex) (.inr col) (rowEdges (start+1) tail)) = _
      rw [rowMatch, if_neg ne, same, ih]
      rfl

private theorem columnsEqual (xs ys : List Nat)
    (agree : ∀ i c, decide (rowLookup xs i = some c) = decide (rowLookup ys i = some c)) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h := agree 0 y
      change false = decide ((some y : Option Nat) = some y) at h
      rw [decide_eq_true rfl] at h
      contradiction
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := agree 0 x
      change decide ((some x : Option Nat) = some x) = false at h
      rw [decide_eq_true rfl] at h
      contradiction
    | cons y ys =>
      have heads := agree 0 x
      change decide ((some x : Option Nat) = some x) = decide ((some y : Option Nat) = some x) at heads
      have yh := Option.some.inj (of_decide_eq_true (heads.symm.trans (decide_eq_true rfl)))
      cases yh
      exact congrArg (List.cons x) (ih ys (fun i c => agree (i+1) c))

/-- A summary answering the fixed two-free-vertex affine tests identifies
    each matching in any chosen family, including all permutation matchings.
    A single decoder answers queries for every column list in the family. -/
theorem matchingSummariesInjective {S : Type} (family : List Nat → Prop)
    (summary : List Nat → S) (answer : S → Nat → Nat → Bool)
    (correct : ∀ xs, family xs → ∀ i col, answer (summary xs) i col = true ↔
        IsAffine (fun s t => graphRead (pin (.inl i : Vertex) (.inr col) s t) (rowEdges 0 xs)))
    (xs ys : List Nat) (hx : family xs) (hy : family ys)
    (same : summary xs = summary ys) : xs = ys := by
  apply columnsEqual
  intro i col
  have query (zs : List Nat) (hz : family zs) :
      answer (summary zs) i col = true ↔ decide (rowLookup zs i = some col) = false := by
    have test := affineIffMissing (.inl i : Vertex) (.inr col) (fun h => Sum.noConfusion h)
      (rowEdges 0 zs) (rowsLoopless zs 0)
    have bound := incidence zs 0 i col
    rw [Nat.zero_add] at bound
    rw [←bound]
    exact (correct zs hz i col).trans test
  have left := query xs hx
  have right := query ys hy
  rw [same] at left
  have iff := left.symm.trans right
  cases xval : decide (rowLookup xs i = some col) <;> cases yval : decide (rowLookup ys i = some col)
  · rfl
  · exact Bool.noConfusion (yval.symm.trans (iff.mp xval))
  · exact Bool.noConfusion (xval.symm.trans (iff.mpr yval))
  · rfl

/-- The same determination of the matching holds for summaries answering
    the constant-zero test on each pinned pair. -/
theorem zeroSummariesInjective {S : Type} (family : List Nat → Prop)
    (summary : List Nat → S) (answer : S → Nat → Nat → Bool)
    (correct : ∀ xs, family xs → ∀ i col, answer (summary xs) i col = true ↔
        IsZero (fun s t => graphRead (pin (.inl i : Vertex) (.inr col) s t) (rowEdges 0 xs)))
    (xs ys : List Nat) (hx : family xs) (hy : family ys)
    (same : summary xs = summary ys) : xs = ys := by
  apply matchingSummariesInjective family summary answer _ xs ys hx hy same
  intro zs hz i col
  have distinct : (Sum.inl i : Vertex) ≠ .inr col := fun h => Sum.noConfusion h
  have loopless := rowsLoopless zs 0
  exact ((correct zs hz i col).trans (zeroIffMissing _ _ distinct _ loopless)).trans
    (affineIffMissing _ _ distinct _ loopless).symm

private theorem rowPresent (cols : List Nat) (i col : Nat) (present : rowLookup cols i = some col) :
    i < cols.length ∧ col ∈ cols := by
  induction cols generalizing i with
  | nil => exact Option.noConfusion present
  | cons h rest ih =>
    cases i with
    | zero =>
      have eq : h = col := Option.some.inj present
      cases eq
      exact ⟨Nat.zero_lt_succ _, List.Mem.head rest⟩
    | succ i =>
      have prev := ih i present
      exact ⟨Nat.succ_lt_succ prev.1, List.Mem.tail h prev.2⟩

/-- Only the m² queries on the public board need be answered. In particular
    this specializes to summaries of all perfect matchings of K_{m,m}. -/
theorem finiteBoardSummariesInjective {S : Type} (m : Nat) (family : List Nat → Prop)
    (board : ∀ zs, family zs → zs.length ≤ m ∧ ∀ c ∈ zs, c < m)
    (summary : List Nat → S) (answer : S → Nat → Nat → Bool)
    (correct : ∀ xs, family xs → ∀ i col, i < m → col < m →
      (answer (summary xs) i col = true ↔
        IsAffine (fun s t => graphRead (pin (.inl i : Vertex) (.inr col) s t) (rowEdges 0 xs))))
    (xs ys : List Nat) (hx : family xs) (hy : family ys)
    (same : summary xs = summary ys) : xs = ys := by
  let extended := fun (z : S) (i col : Nat) =>
    if i < m ∧ col < m then answer z i col else true
  apply matchingSummariesInjective family summary extended _ xs ys hx hy same
  intro zs hz i col
  by_cases inside : i < m ∧ col < m
  · unfold extended
    rw [if_pos inside]
    exact correct zs hz i col inside.1 inside.2
  · have missing : ¬ rowLookup zs i = some col := by
      intro present
      have bounds := rowPresent zs i col present
      have ok := board zs hz
      exact inside ⟨Nat.lt_of_lt_of_le bounds.1 ok.1, ok.2 col bounds.2⟩
    have edge := incidence zs 0 i col
    rw [Nat.zero_add, decide_eq_false missing] at edge
    have affine := (affineIffMissing (.inl i : Vertex) (.inr col) (fun h => Sum.noConfusion h)
      (rowEdges 0 zs) (rowsLoopless zs 0)).mpr edge
    unfold extended
    rw [if_neg inside]
    exact ⟨fun _ => affine, fun _ => rfl⟩

end ForestReadQueries
