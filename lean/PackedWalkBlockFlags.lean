import Std

namespace PackedWalkBlockFlags

structure Seed (Column Label : Type) where
  start : Column
  moves : List Label

def advance (step : C → L → C) (s : Seed C L) : Seed C L :=
  match s.moves with
  | [] => s
  | l :: ls => ⟨step s.start l, ls⟩

def jump (step : C → L → C) : Nat → Seed C L → Seed C L
  | 0, s => s
  | n+1, s => jump step n (advance step s)

/-- Directly inspect the selected entry of each row. -/
def scan (step : C → L → C) : List (C → Bool) → Seed C L → Bool
  | [], _ => true
  | m :: rows, s => m s.start && scan step rows (advance step s)

/-- Each vector depends on a single row mask. The remaining inputs, giving
the initial column and the public transitions, only choose the vector index. -/
def rowTables (step : C → L → C) : List (C → Bool) → List (Seed C L → Bool)
  | [] => []
  | m :: rows => (fun s => m s.start) ::
      (rowTables step rows).map (fun f s => f (advance step s))

def flag (step : C → L → C) (rows : List (C → Bool)) (s : Seed C L) : Bool :=
  (rowTables step rows).all (fun f => f s)

theorem row_table_intersection (step : C → L → C) (rows : List (C → Bool)) (s : Seed C L) :
    flag step rows s = scan step rows s := by
  induction rows generalizing s with
  | nil => rfl
  | cons m rows ih =>
    change (m s.start && _) = (m s.start && _)
    rw [List.all_map]
    exact congrArg (m s.start && ·) (ih (advance step s))

/-- The final row is inspected before its next transition. A table for r rows
can therefore be addressed by a starting column and only r−1 move labels. -/
theorem short_seed (step : C → L → C) (rows : List (C → Bool)) (z : C) (ls : List L) :
    scan step rows ⟨z, ls.take (rows.length-1)⟩ = scan step rows ⟨z, ls⟩ := by
  induction rows generalizing z ls with
  | nil => rfl
  | cons m rest ih =>
    cases rest with
    | nil => simp [scan]
    | cons m' rs =>
      cases ls with
      | nil => rfl
      | cons l ls =>
        simp only [List.length_cons, Nat.add_sub_cancel, List.take_succ_cons, scan, advance]
        exact congrArg (m z && ·) (ih (step z l) ls)

theorem scan_append (step : C → L → C) (xs ys : List (C → Bool)) (s : Seed C L) :
    scan step (xs ++ ys) s = (scan step xs s && scan step ys (jump step xs.length s)) := by
  induction xs generalizing s with
  | nil => simp [scan, jump]
  | cons x xs ih =>
    simp only [List.cons_append, scan, List.length_cons, jump, ih, Bool.and_assoc]

/-- A new block starts at the column actually reached by the full walk.
Its Boolean table needs no labels from adjacent blocks. -/
def blockFlags (step : C → L → C) : List (List (C → Bool)) → Seed C L → List Bool
  | [], _ => []
  | rows :: rest, s =>
    flag step rows ⟨s.start, s.moves.take (rows.length-1)⟩ ::
      blockFlags step rest (jump step rows.length s)

theorem whole_walk (step : C → L → C) (blocks : List (List (C → Bool))) (s : Seed C L) :
    (blockFlags step blocks s).all id = scan step blocks.flatten s := by
  induction blocks generalizing s with
  | nil => rfl
  | cons rows blocks ih =>
    cases s with
    | mk z ls =>
      simp only [blockFlags, List.all_cons, id_eq, row_table_intersection, short_seed,
        List.flatten_cons, scan_append, ih]

/-- A table chunk contains one bit per local seed. The row records of that
chunk are ANDed wordwise, once during preprocessing. -/
def intersectWords {w : Nat} : List (BitVec w) → BitVec w
  | [] => BitVec.allOnes w
  | v :: vs => v &&& intersectWords vs

theorem intersect_word_bit {w : Nat} (vs : List (BitVec w)) (i : Fin w) :
    (intersectWords vs).getLsbD i = vs.all (fun v => v.getLsbD i) := by
  induction vs with
  | nil => simp [intersectWords, i.isLt]
  | cons v vs ih => simp only [intersectWords, BitVec.getLsbD_and, ih, List.all_cons]

/-- A packed word stores the negated (miss) flags, little endian. -/
def packMisses (flags : List Bool) : BitVec (flags.map (!·)).length :=
  BitVec.ofBoolListLE (flags.map (!·))

theorem zero_test (flags : List Bool) : packMisses flags = 0 ↔ flags.all id = true := by
  constructor
  · intro h
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have eq := congrArg (fun v : BitVec (flags.map (!·)).length => v.getLsbD i) h
    simpa [packMisses, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using eq
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have lt : i < flags.length := by simpa using hi
    have bit := List.all_eq_true.mp h flags[i] (List.getElem_mem lt)
    simp [packMisses, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt, id_eq] at bit ⊢
    exact bit

/-- Grouping any number of consecutive flags into native words and testing
each word for zero gives exactly the answer of the direct traversal. -/
theorem grouped_zero_tests (step : C → L → C) (blocks : List (List (C → Bool)))
    (s : Seed C L) (groups : List (List Bool)) (packed : groups.flatten = blockFlags step blocks s) :
    (∀ g ∈ groups, packMisses g = 0) ↔ scan step blocks.flatten s = true := by
  rw [← whole_walk, ← packed, List.all_eq_true]
  constructor
  · intro accept b hb
    obtain ⟨g, hg, hbg⟩ := List.mem_flatten.mp hb
    exact List.all_eq_true.mp ((zero_test g).mp (accept g hg)) b hbg
  · intro accept g hg
    exact (zero_test g).mpr (List.all_eq_true.mpr (fun b hb =>
      accept b (List.mem_flatten.mpr ⟨g, hg, hb⟩)))

#print axioms whole_walk
#print axioms intersect_word_bit
#print axioms grouped_zero_tests

end PackedWalkBlockFlags
