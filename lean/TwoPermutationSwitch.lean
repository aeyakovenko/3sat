import Std

namespace TwoPermutationSwitch

/-- Rows record the label before and after its row-specific operation. -/
def entries (mark : α → Bool) (rows : List (α × α)) : Nat :=
  rows.countP (fun row => !mark row.1 && mark row.2)

def exits (mark : α → Bool) (rows : List (α × α)) : Nat :=
  rows.countP (fun row => mark row.1 && !mark row.2)

private theorem count_sides (mark : α → Bool) (rows : List (α × α)) :
    (rows.map Prod.fst).countP mark + entries mark rows =
    (rows.map Prod.snd).countP mark + exits mark rows := by
  induction rows with
  | nil => simp [entries, exits]
  | cons row rows ih =>
    obtain ⟨old, new⟩ := row
    unfold entries exits at *
    simp only [List.countP_map] at ih
    cases h : mark old <;> cases k : mark new <;>
      simp [List.countP_cons, h, k] <;> omega

/-- For every subset of labels the number of activated rows entering it
    equals the number leaving it. Singleton subsets give vertex balance. -/
theorem cut_balance (mark : α → Bool) (rows : List (α × α))
    (snapshots : (rows.map Prod.fst).Perm (rows.map Prod.snd)) :
    entries mark rows = exits mark rows := by
  have eqCount := snapshots.countP_eq mark
  have eqSides := count_sides mark rows
  omega

inductive Label where
  | vertex : Nat → Bool → Label
  | extra : Nat → Label
  deriving DecidableEq

def transpose (left right chosen : Label) : Label :=
  if chosen = left then right else if chosen = right then left else chosen

def prefixParity (switch : Nat → Bool) : Nat → Bool
  | 0 => false
  | n+1 => prefixParity switch n ^^ switch n

/-- The color records the lane at layer zero reached by tracing switches back. -/
def laneColor (switch : Nat → Bool) : Label → Bool
  | .vertex layer lane => lane ^^ prefixParity switch layer
  | .extra _ => false

theorem switch_preserves_color (switch : Nat → Bool) (i : Nat) (s : Bool) :
    laneColor switch (.vertex (i+1) (s ^^ switch i)) =
    laneColor switch (.vertex i s) := by
  cases s <;> cases h : switch i <;> cases k : prefixParity switch i <;>
    simp [laneColor, prefixParity, h, k]

def ordinaryAfter (switch : Nat → Bool) (row : Option (Nat × Bool) × Label) : Label :=
  match row.1 with
  | none => row.2
  | some (i,s) =>
      transpose (.vertex i s) (.vertex (i+1) (s ^^ switch i)) row.2

theorem ordinary_color (switch : Nat → Bool) (row : Option (Nat × Bool) × Label) :
    laneColor switch (ordinaryAfter switch row) = laneColor switch row.2 := by
  obtain ⟨edge, chosen⟩ := row
  cases edge with
  | none => rfl
  | some pair =>
    obtain ⟨i,s⟩ := pair
    simp only [ordinaryAfter, transpose]
    split
    · next h => simpa [h] using switch_preserves_color switch i s
    · split
      · next h => simpa [h] using (switch_preserves_color switch i s).symm
      · rfl

private theorem ordinary_counts (switch : Nat → Bool)
    (rows : List (Option (Nat × Bool) × Label)) :
    (rows.map (ordinaryAfter switch)).countP (laneColor switch) =
      (rows.map Prod.snd).countP (laneColor switch) := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    simp [List.countP_cons, ordinary_color, ih]

/-- The distinguished closing row swaps (m,0) and (0,0). All other rows are
    identity rows or layer-edge transpositions. If the closing row holds an
    endpoint and both snapshots have the same multiset, the switch parity
    through layer m is even. The theorem also allows spare labels and rows. -/
theorem closing_implies_even (switch : Nat → Bool) (m : Nat)
    (closing : Label) (rows : List (Option (Nat × Bool) × Label))
    (active : closing = .vertex m false ∨ closing = .vertex 0 false)
    (snapshots :
      (closing :: rows.map Prod.snd).Perm
        (transpose (.vertex m false) (.vertex 0 false) closing ::
          rows.map (ordinaryAfter switch))) :
    prefixParity switch m = false := by
  have counts := snapshots.countP_eq (laneColor switch)
  simp only [List.countP_cons, ordinary_counts] at counts
  rcases active with h | h
  · subst closing
    simpa [transpose, laneColor, prefixParity] using counts
  · subst closing
    cases m with
    | zero => rfl
    | succ m =>
      cases h : prefixParity switch (m+1) <;>
        simp_all [transpose, laneColor, prefixParity]

/-- Listed in reverse layer order. Each activated path row is assigned its
    source vertex. The switch transposition moves it to the next vertex. -/
def pathRows (switch : Nat → Bool) : Nat → List (Option (Nat × Bool) × Label)
  | 0 => []
  | i+1 => (some (i,prefixParity switch i), .vertex i (prefixParity switch i)) ::
      pathRows switch i

private theorem path_balance (switch : Nat → Bool) (m : Nat) :
    ((Label.vertex m (prefixParity switch m)) ::
      (pathRows switch m).map Prod.snd).Perm
    ((Label.vertex 0 false) :: (pathRows switch m).map (ordinaryAfter switch)) := by
  induction m with
  | zero => exact List.Perm.refl _
  | succ i ih =>
    simp only [pathRows, List.map_cons]
    have target :
        ordinaryAfter switch
          (some (i,prefixParity switch i), .vertex i (prefixParity switch i)) =
          .vertex (i+1) (prefixParity switch (i+1)) := by
      simp [ordinaryAfter, transpose, prefixParity]
    rw [target]
    exact (List.Perm.cons _ ih).trans (List.Perm.swap _ _ _)

private theorem source_layer_lt (switch : Nat → Bool) (m : Nat)
    (v : Label) (mem : v ∈ (pathRows switch m).map Prod.snd) :
    ∃ i, i < m ∧ v = .vertex i (prefixParity switch i) := by
  induction m with
  | zero => simp [pathRows] at mem
  | succ i ih =>
    simp only [pathRows, List.map_cons, List.mem_cons] at mem
    rcases mem with h | h
    · exact ⟨i, Nat.lt_succ_self _, h⟩
    · obtain ⟨j, lt, eq⟩ := ih h
      exact ⟨j, Nat.lt_trans lt (Nat.lt_succ_self _), eq⟩

private theorem path_unique (switch : Nat → Bool) (m : Nat) :
    ((Label.vertex m (prefixParity switch m)) ::
      (pathRows switch m).map Prod.snd).Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro mem
    obtain ⟨j, lt, eq⟩ := source_layer_lt switch m _ mem
    cases eq
    exact Nat.lt_irrefl _ lt
  · induction m with
    | zero => simp [pathRows]
    | succ i ih =>
      simp only [pathRows, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro mem
      obtain ⟨j, lt, eq⟩ := source_layer_lt switch i _ mem
      cases eq
      exact Nat.lt_irrefl _ lt

/-- Even parity gives an explicit activated path and closing row with
    distinct input labels and exactly the same set of output labels. The
    ambient row permutation can additionally contain any disjoint fixed rows. -/
theorem even_realizes_cycle (switch : Nat → Bool) (m : Nat)
    (even : prefixParity switch m = false) :
    let old := Label.vertex m false :: (pathRows switch m).map Prod.snd
    let new := transpose (.vertex m false) (.vertex 0 false) (.vertex m false) ::
      (pathRows switch m).map (ordinaryAfter switch)
    old.Nodup ∧ old.Perm new := by
  constructor
  · simpa [even] using path_unique switch m
  · simpa [even, transpose] using path_balance switch m

end TwoPermutationSwitch
