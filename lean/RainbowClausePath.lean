import Std

namespace RainbowClausePath

structure Literal (Var : Type) where
  variableName : Var
  required : Bool

def Literal.holds {Var} (lit : Literal Var) (x : Var → Bool) : Bool :=
  x lit.variableName == lit.required

/-- Colors name occurrences, not variable names or signed literals. -/
abbrev Color := Nat × Nat

def inRow (i width : Nat) : List Color := (List.range width).map (Prod.mk i)

def allOccurrences (rows : Nat) (width : Nat → Nat) : List Color :=
  (List.range rows).flatMap (fun i => inRow i (width i))

theorem in_row {u : Color} {i w} : u ∈ inRow i w ↔ u.1 = i ∧ u.2 < w := by
  constructor
  · intro mem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp mem
    exact ⟨rfl, List.mem_range.mp hj⟩
  · obtain ⟨a, b⟩ := u
    rintro ⟨rfl, hb⟩
    exact List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩

theorem occurrence {rows width} {u : Color} :
    u ∈ allOccurrences rows width ↔ u.1 < rows ∧ u.2 < width u.1 := by
  constructor
  · intro mem
    obtain ⟨i, hi, row⟩ := List.mem_flatMap.mp mem
    obtain ⟨eq, slot⟩ := in_row.mp row
    rw [eq]
    exact ⟨List.mem_range.mp hi, slot⟩
  · rintro ⟨hi, slot⟩
    exact List.mem_flatMap.mpr ⟨u.1, List.mem_range.mpr hi, in_row.mpr ⟨rfl, slot⟩⟩

theorem distinct_occurrences (rows width) : (allOccurrences rows width).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    exact List.nodup_range.imp (fun ne eq => ne (congrArg Prod.snd eq))
  · apply List.nodup_range.imp
    intro i j ne x hx y hy eq
    exact ne ((in_row.mp hx).1.symm.trans ((congrArg Prod.fst eq).trans (in_row.mp hy).1))

variable {Var : Type}

def variableColors (rows : Nat) (width : Nat → Nat) (formula : Color → Literal Var)
    (x : Var → Bool) : List Color :=
  (allOccurrences rows width).filter (fun c => !(formula c).holds x)

def clauseColors (rows : Nat) (choose : Nat → Nat) : List Color :=
  (List.range rows).map (fun i => (i, choose i))

theorem variable_path_uses {rows width} {formula : Color → Literal Var} {x : Var → Bool}
    {c : Color} : c ∈ variableColors rows width formula x ↔
      c.1 < rows ∧ c.2 < width c.1 ∧ (formula c).holds x = false := by
  simp [variableColors, occurrence, and_assoc]

theorem clause_path_uses {rows choose} {c : Color} : c ∈ clauseColors rows choose ↔
    c.1 < rows ∧ c.2 = choose c.1 := by
  constructor
  · intro mem
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp mem
    exact ⟨List.mem_range.mp hi, rfl⟩
  · obtain ⟨i, j⟩ := c
    rintro ⟨hi, chosen⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, Prod.ext rfl chosen.symm⟩

theorem rainbow_iff_selected_true (rows : Nat) (width : Nat → Nat) (formula : Color → Literal Var)
    (x : Var → Bool) (choose : Nat → Nat) (legal : ∀ i < rows, choose i < width i) :
    (variableColors rows width formula x ++ clauseColors rows choose).Nodup ↔
      ∀ i < rows, (formula (i, choose i)).holds x = true := by
  constructor
  · intro rainbow i hi
    by_cases good : (formula (i, choose i)).holds x = true
    · exact good
    · have bad : (formula (i, choose i)).holds x = false := by cases h : (formula (i, choose i)).holds x <;> simp_all
      have left := (variable_path_uses (c := (i, choose i))).mpr ⟨hi, legal i hi, bad⟩
      have right := (clause_path_uses (c := (i, choose i)) (choose := choose)).mpr ⟨hi, rfl⟩
      exact False.elim ((List.pairwise_append.mp rainbow).2.2 _ left _ right rfl)
  · intro good
    apply List.pairwise_append.mpr
    refine ⟨(distinct_occurrences rows width).filter _, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact List.nodup_range.imp (fun ne eq => ne (congrArg Prod.fst eq))
    · rintro c hc _ hr rfl
      obtain ⟨row, slot, bad⟩ := variable_path_uses.mp hc
      obtain ⟨_, picked⟩ := clause_path_uses.mp hr
      have eq : c = (c.1, choose c.1) := Prod.ext rfl picked
      have yes := good c.1 row
      rw [← eq] at yes
      simp [yes] at bad

/-- Traversal can group occurrences by variable rather than by clause. -/
theorem reordered_paths {rows width} (formula : Color → Literal Var) (x : Var → Bool)
    (choose : Nat → Nat) (legal : ∀ i < rows, choose i < width i) (left right : List Color)
    (visitsVariables : left.Perm (variableColors rows width formula x))
    (visitsClauses : right.Perm (clauseColors rows choose)) :
    (left ++ right).Nodup ↔ ∀ i < rows, (formula (i, choose i)).holds x = true :=
  (visitsVariables.append visitsClauses).nodup_iff.trans
    (rainbow_iff_selected_true rows width formula x choose legal)

theorem rainbow_iff_satisfiable (rows : Nat) (width : Nat → Nat) (formula : Color → Literal Var) :
    (∃ x choose, (∀ i < rows, choose i < width i) ∧
      (variableColors rows width formula x ++ clauseColors rows choose).Nodup) ↔
    ∃ x : Var → Bool, ∀ i < rows, ∃ j < width i, (formula (i, j)).holds x = true := by
  constructor
  · rintro ⟨x, choose, legal, rainbow⟩
    have good := (rainbow_iff_selected_true rows width formula x choose legal).mp rainbow
    exact ⟨x, fun i hi => ⟨choose i, legal i hi, good i hi⟩⟩
  · classical
    rintro ⟨x, sat⟩
    let choose (i : Nat) := if hi : i < rows then Classical.choose (sat i hi) else 0
    have spec (i : Nat) (hi : i < rows) :
        choose i < width i ∧ (formula (i, choose i)).holds x = true := by
      simpa [choose, hi] using Classical.choose_spec (sat i hi)
    have legal := fun i hi => (spec i hi).1
    exact ⟨x, choose, legal, (rainbow_iff_selected_true rows width formula x choose legal).mpr
      (fun i hi => (spec i hi).2)⟩

section Fill

variable {Vertex Label : Type} [DecidableEq Vertex] [DecidableEq Label]

/-- Distinct namespaces keep a vertex from colliding with an occurrence color. -/
def exchange (v : Vertex) (c : Label) : Vertex ⊕ Label → Vertex ⊕ Label
  | .inl x => if x = v then .inr c else .inl x
  | .inr y => if y = c then .inl v else .inr y

theorem exchange_twice (v : Vertex) (c : Label) (x : Vertex ⊕ Label) :
    exchange v c (exchange v c x) = x := by
  cases x with
  | inl x => by_cases same : x = v <;> simp [exchange, same]
  | inr y => by_cases same : y = c <;> simp [exchange, same]

def fill : List (Vertex × Label) → Vertex ⊕ Label → Vertex ⊕ Label
  | [], x => x
  | (v,c)::rest, x => exchange v c (fill rest x)

def undoFill : List (Vertex × Label) → Vertex ⊕ Label → Vertex ⊕ Label
  | [], x => x
  | (v,c)::rest, x => undoFill rest (exchange v c x)

theorem fill_permutation (pairs : List (Vertex × Label)) (x : Vertex ⊕ Label) :
    undoFill pairs (fill pairs x) = x ∧ fill pairs (undoFill pairs x) = x := by
  induction pairs generalizing x with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    obtain ⟨v,c⟩ := head
    constructor
    · simpa only [fill, undoFill, exchange_twice] using (ih x).1
    · simp only [fill, undoFill, (ih (exchange v c x)).2, exchange_twice]

theorem unused_vertex (pairs : List (Vertex × Label)) (v : Vertex)
    (free : v ∉ pairs.map Prod.fst) : fill pairs (.inl v) = .inl v := by
  induction pairs with
  | nil => rfl
  | cons head xs ih =>
    obtain ⟨u,c⟩ := head
    have ne : v ≠ u := fun e => free (by simp [e])
    have tail := ih (fun h => free (by simp [h]))
    simp [fill, tail, exchange, ne]

theorem unused_color (pairs : List (Vertex × Label)) (c : Label)
    (free : c ∉ pairs.map Prod.snd) : fill pairs (.inr c) = .inr c := by
  induction pairs with
  | nil => rfl
  | cons head xs ih =>
    obtain ⟨v,d⟩ := head
    have ne : c ≠ d := fun e => free (by simp [e])
    have tail := ih (fun h => free (by simp [h]))
    simp [fill, tail, exchange, ne]

theorem active_pair (pairs : List (Vertex × Label)) (v : Vertex) (c : Label)
    (vertices : (pairs.map Prod.fst).Nodup) (colors : (pairs.map Prod.snd).Nodup)
    (active : (v,c) ∈ pairs) : fill pairs (.inl v) = .inr c ∧ fill pairs (.inr c) = .inl v := by
  induction pairs with
  | nil => simp at active
  | cons head xs ih =>
    obtain ⟨u,d⟩ := head
    obtain ⟨uFresh, vTail⟩ := List.nodup_cons.mp vertices
    obtain ⟨dFresh, cTail⟩ := List.nodup_cons.mp colors
    rcases List.mem_cons.mp active with eq | old
    · cases eq
      simp [fill, unused_vertex xs _ uFresh, unused_color xs _ dFresh, exchange]
    · obtain ⟨outV, outC⟩ := ih vTail cTail old
      have vne : v ≠ u := fun e => uFresh (List.mem_map.mpr ⟨(v,c), old, e⟩)
      have cne : c ≠ d := fun e => dFresh (List.mem_map.mpr ⟨(v,c), old, e⟩)
      simp [fill, outV, outC, exchange, vne, cne]

end Fill

end RainbowClausePath
