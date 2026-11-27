import Std

/-! Local obstructions for replacing independent proper ternary clauses, and
an explicit five-clause existential replacement of one such clause. -/
namespace LocalClausePorts

theorem missing_clause_budget (d : Nat) (h : 3 * d ≤ 2 * (d + 1)) : d ≤ 2 := by
  omega

def zeros (a b c d e f : Bool) : Nat :=
  (!a).toNat + (!b).toNat + (!c).toNat + (!d).toNat + (!e).toNat + (!f).toNat

def checkPairs (a b c d e f s t u v : Bool) : Bool :=
  (a || b || (v ^^ s)) && (c || d || (v ^^ t)) && (e || f || (v ^^ u))

/-- The three pairs may be in any order. With precisely three zero ports at
most one pair activates its auxiliary unit. Even the two constant assignments
to all the auxiliaries suffice, independently of their relative signs. -/
theorem three_zeros_signed_pairs : ∀ a b c d e f s t u : Bool,
    zeros a b c d e f = 3 →
    ∃ v : Bool, checkPairs a b c d e f s t u v = true := by
  decide

def literal {ι : Type} (assignment : ι → Bool) (l : ι × Bool) : Bool :=
  assignment l.1 ^^ l.2

/-- The auxiliary variables may coincide. No assumption on their names or
signs is needed. The six ports occur exactly once in these three rows. -/
theorem two_missing_residue {ι : Type} (a b c d e f : Bool)
    (l₀ l₁ l₂ : ι × Bool) (h : zeros a b c d e f = 3) :
    ∃ assignment : ι → Bool,
      ((a || b || literal assignment l₀) &&
       (c || d || literal assignment l₁) &&
       (e || f || literal assignment l₂)) = true := by
  obtain ⟨v, hv⟩ := three_zeros_signed_pairs a b c d e f l₀.2 l₁.2 l₂.2 h
  exact ⟨fun _ => v, hv⟩

theorem opposite_unit_split : ∀ a b c : Bool,
    (∃ v : Bool, ((a || b || v) && (c || b || !v)) = true) ↔
      (a || b || c) = true := by decide

inductive Var where
  | a | b | c | x | y | z | s
  deriving Repr, BEq, DecidableEq

open Var

abbrev Lit := Var × Bool

/-- The Boolean flag is true for a negative occurrence. -/
def fiveRows : List (List Lit) :=
  [[(a,false), (y,false), (z,false)],
   [(b,false), (x,false), (z,true)],
   [(c,false), (x,true),  (y,true)],
   [(x,false), (y,true),  (z,false)],
   [(x,true),  (y,false), (z,true)]]

def proper (row : List Lit) : Prop :=
  row.length = 3 ∧ (row.map Prod.fst).Nodup

instance (row : List Lit) : Decidable (proper row) := by
  unfold proper
  infer_instance

theorem all_rows_proper : ∀ row ∈ fiveRows, proper row := by decide

def occurrences (v : Var) (neg : Bool) : Nat :=
  fiveRows.flatten.count (v, neg)

theorem port_occurrences : ∀ v ∈ [a,b,c],
    occurrences v false = 1 ∧ occurrences v true = 0 := by decide

theorem aux_occurrences : ∀ v ∈ [x,y,z],
    occurrences v false = 2 ∧ occurrences v true = 2 := by decide

abbrev Cube := Bool × Bool × Bool

def valuesWithSwitch (port aux : Cube) (switch : Bool) : Var → Bool
  | a => port.1
  | b => port.2.1
  | c => port.2.2
  | x => aux.1
  | y => aux.2.1
  | z => aux.2.2
  | s => switch

def acceptWithSwitch (formula : List (List Lit)) (port aux : Cube) (switch : Bool) : Bool :=
  formula.all fun row => row.any (literal (valuesWithSwitch port aux switch))

def accept (formula : List (List Lit)) (port aux : Cube) : Bool :=
  acceptWithSwitch formula port aux false

def cubePoints : List Cube :=
  [(false,false,false), (false,false,true), (false,true,false), (false,true,true),
   (true,false,false),  (true,false,true),  (true,true,false),  (true,true,true)]

theorem cube_nodup : cubePoints.Nodup := by decide
theorem cube_complete : ∀ x y z : Bool, (x,y,z) ∈ cubePoints := by decide

def extensionCount (port : Cube) : Nat :=
  (cubePoints.filter (accept fiveRows port)).length

theorem five_row_model_count : ∀ a b c : Bool,
    extensionCount (a,b,c) = 2 * (a.toNat + b.toNat + c.toNat) := by decide

theorem five_row_projection : ∀ a b c : Bool,
    (∃ x y z : Bool, accept fiveRows (a,b,c) (x,y,z) = true) ↔
      (a || b || c) = true := by decide

theorem deletion_changes_projection : ∀ i : Fin 5,
    ∃ x y z : Bool, accept (fiveRows.eraseIdx i.val) (false,false,false) (x,y,z) = true := by
  decide

/-- The middle five rows restrict (x,y,z) to Hamming weight two. The last
three then force s false. Each zero among x,y,z needs its own true port. -/
def elevenRows : List (List Lit) :=
  [[(a,false), (s,false), (x,false)],
   [(b,false), (s,false), (y,false)],
   [(c,false), (s,false), (z,false)],
   [(x,false), (y,false), (z,false)],
   [(x,true),  (y,false), (z,false)],
   [(x,false), (y,true),  (z,false)],
   [(x,false), (y,false), (z,true)],
   [(x,true),  (y,true),  (z,true)],
   [(s,true),  (x,true),  (y,true)],
   [(s,true),  (x,true),  (z,true)],
   [(s,true),  (y,true),  (z,true)]]

theorem eleven_rows_proper : ∀ row ∈ elevenRows, proper row := by decide

theorem eleven_occurrences :
    (∀ v ∈ [a,b,c], elevenRows.flatten.count (v,false) = 1 ∧
                     elevenRows.flatten.count (v,true) = 0) ∧
    (∀ v ∈ [s,x,y,z], elevenRows.flatten.count (v,false) ≥ 2 ∧
                       elevenRows.flatten.count (v,true) ≥ 2) := by decide

set_option synthInstance.maxSize 512 in
theorem eleven_truth_table : ∀ a b c switch x y z : Bool,
    acceptWithSwitch elevenRows (a,b,c) (x,y,z) switch = true ↔
    switch = false ∧
      ((a = true ∧ (x,y,z) = (false,true,true)) ∨
       (b = true ∧ (x,y,z) = (true,false,true)) ∨
       (c = true ∧ (x,y,z) = (true,true,false))) := by decide

def countWithSwitch (formula : List (List Lit)) (port : Cube) : Nat :=
  ([false,true].map fun switch =>
    (cubePoints.filter fun aux => acceptWithSwitch formula port aux switch).length).sum

theorem eleven_model_count : ∀ a b c : Bool,
    countWithSwitch elevenRows (a,b,c) = a.toNat + b.toNat + c.toNat := by decide

theorem eleven_private_zero_boundary : ∀ i : Fin 11,
    ∃ switch x y z : Bool,
      acceptWithSwitch (elevenRows.eraseIdx i.val) (false,false,false) (x,y,z) switch = true ∧
      acceptWithSwitch elevenRows (false,false,false) (x,y,z) switch = false := by decide

/-- Zeros among (x,y,z) encode a nonempty subset of the true ports. -/
def eightRows : List (List Lit) :=
  elevenRows.take 3 ++
  [[(x,true),  (y,true),  (z,true)],
   [(s,true),  (x,false), (y,false)],
   [(s,true),  (x,false), (y,true)],
   [(s,true),  (x,true),  (y,false)],
   [(s,true),  (x,true),  (z,false)]]

theorem eight_rows_proper : ∀ row ∈ eightRows, proper row := by decide

theorem eight_occurrences :
    (∀ v ∈ [a,b,c], eightRows.flatten.count (v,false) = 1 ∧
                     eightRows.flatten.count (v,true) = 0) ∧
    ([s,x,y,z].map fun v =>
      (eightRows.flatten.count (v,false), eightRows.flatten.count (v,true))) =
    [(3,4),(3,3),(3,2),(2,1)] := by decide

theorem eight_truth_table : ∀ a b c switch x y z : Bool,
    acceptWithSwitch eightRows (a,b,c) (x,y,z) switch =
    (!switch && !(x && y && z) && (a || x) && (b || y) && (c || z)) := by decide

theorem eight_model_count : ∀ a b c : Bool,
    countWithSwitch eightRows (a,b,c) = 2 ^ (a.toNat + b.toNat + c.toNat) - 1 := by decide

theorem eight_private_zero_boundary : ∀ i : Fin 8,
    ∃ switch x y z : Bool,
      acceptWithSwitch (eightRows.eraseIdx i.val) (false,false,false) (x,y,z) switch = true ∧
      acceptWithSwitch eightRows (false,false,false) (x,y,z) switch = false := by decide

/-- The last four switched clauses partition the cube at s=true into four
forbidden edges. Each of its variables has at least two occurrences per sign. -/
def balancedEightRows : List (List Lit) :=
  eightRows.take 6 ++
  [[(s,true), (x,true), (z,false)],
   [(s,true), (x,true), (z,true)]]

theorem balanced_eight_rows_proper : ∀ row ∈ balancedEightRows, proper row := by decide

theorem balanced_eight_occurrences :
    (∀ v ∈ [a,b,c], balancedEightRows.flatten.count (v,false) = 1 ∧
                     balancedEightRows.flatten.count (v,true) = 0) ∧
    ([s,x,y,z].map fun v =>
      (balancedEightRows.flatten.count (v,false), balancedEightRows.flatten.count (v,true))) =
    [(3,4),(3,3),(2,2),(2,2)] := by decide

theorem balanced_eight_truth_table : ∀ a b c switch x y z : Bool,
    acceptWithSwitch balancedEightRows (a,b,c) (x,y,z) switch =
    acceptWithSwitch eightRows (a,b,c) (x,y,z) switch := by decide

theorem balanced_eight_model_count : ∀ a b c : Bool,
    countWithSwitch balancedEightRows (a,b,c) = 2 ^ (a.toNat + b.toNat + c.toNat) - 1 := by
  decide

theorem balanced_eight_private_zero_boundary : ∀ i : Fin 8,
    ∃ switch x y z : Bool,
      acceptWithSwitch (balancedEightRows.eraseIdx i.val) (false,false,false) (x,y,z) switch =
        true ∧
      acceptWithSwitch balancedEightRows (false,false,false) (x,y,z) switch = false := by decide

/-- Rows containing a true terminal can be skipped. Every other row must
already be satisfied by the auxiliary assignment. -/
def permitted {ι α : Type} (passes : α → ι → Prop) (enabled : ι → Prop) (w : α) : Prop :=
  ∀ i, passes w i ∨ enabled i

theorem permitted_mono {ι α : Type} {passes : α → ι → Prop}
    {p q : ι → Prop} {w : α} (hpq : ∀ i, p i → q i)
    (hp : permitted passes p w) : permitted passes q w :=
  fun i => (hp i).imp_right (hpq i)

/-- An unsatisfiable zero-port formula associates disjoint witness sets to
distinct singly enabled rows. This uses no width or occurrence condition on
the auxiliary variables. -/
theorem distinct_single_row_witnesses {ι α : Type} {passes : α → ι → Prop}
    (noZero : ∀ w, ¬ ∀ i, passes w i) {r s : ι} (hrs : r ≠ s) {u v : α}
    (hu : permitted passes (· = r) u) (hv : permitted passes (· = s) v) : u ≠ v := by
  rintro rfl
  apply noZero u
  intro i
  rcases hu i with h | rfl
  · exact h
  · exact (hv i).resolve_right hrs

/-- Picking any accepting witness per singly enabled row embeds these row
labels into the witness space. All picked witnesses survive when their rows
are jointly enabled. The label type may list just a subset of the rows. -/
theorem singly_enabled_embed {ι α κ : Type} {passes : α → ι → Prop}
    (noZero : ∀ w, ¬ ∀ i, passes w i) {row : κ → ι}
    (distinct : ∀ k l, row k = row l → k = l) {witness : κ → α}
    (single : ∀ k, permitted passes (· = row k) (witness k)) :
    (∀ k l, witness k = witness l → k = l) ∧
    (∀ k, permitted passes (fun i => ∃ l, i = row l) (witness k)) := by
  constructor
  · intro k l heq
    apply distinct
    exact Classical.byContradiction fun h =>
      distinct_single_row_witnesses noZero h (single k) (single l) heq
  · exact fun k => permitted_mono (fun _ h => ⟨k, h⟩) (single k)

end LocalClausePorts
