import Std

namespace NestedQueryTable

/-- The three query vertices may be labeled in any order, with repetition. -/
inductive Site where
  | x | y | z
  deriving DecidableEq

inductive State (ι : Type) where
  | query (i : ι)
  | result (b : Bool)
  | dead
  deriving DecidableEq

structure Graph (ι : Type) where
  start : State ι
  label : ι → Site
  edge : ι → Bool → State ι

abbrev Input := Site → Bool

def target (p : Input) : Bool := !p .z && (p .x == p .y)

/-- A finite derivation records a genuine halt. There is no time bound, and
    edges can return to any vertex, including their source. -/
inductive Halts {ι : Type} (g : Graph ι) (p : Input) : State ι → Bool → Prop where
  | result : Halts g p (.result b) b
  | query (tail : Halts g p (g.edge i (p (g.label i))) b) :
      Halts g p (.query i) b

private theorem deterministic {ι : Type} {g : Graph ι} {p : Input} {q : State ι} {b c : Bool}
    (h : Halts g p q b) (h' : Halts g p q c) : b = c := by
  induction h with
  | result => cases h'; rfl
  | query _ ih => cases h' with | query tail => exact ih tail

private theorem changeInput {ι : Type} {g : Graph ι} {p p' : Input} {q : State ι} {b : Bool}
    (same : ∀ i, p (g.label i) = p' (g.label i)) (h : Halts g p q b) :
    Halts g p' q b := by
  induction h with
  | result => exact .result
  | @query i _ _ ih => exact .query (by simpa only [same i] using ih)

private theorem allLabels {ι : Type} {g : Graph ι}
    (decides : ∀ p, Halts g p g.start (target p)) (a : Site) :
    ∃ i, g.label i = a := by
  classical
  apply Classical.byContradiction
  intro missing
  let zeros : Input := fun _ => false
  let flip : Input := fun i => decide (i = a)
  have same (i) : zeros (g.label i) = flip (g.label i) := by
    have notLabel : g.label i ≠ a := fun h => missing ⟨i, h⟩
    simp [zeros, flip, notLabel]
  have h := deterministic (changeInput same (decides zeros)) (decides flip)
  cases a <;> simp [target, zeros, flip] at h

private theorem uniqueLabels {g : Graph Site} (all : ∀ a, ∃ i, g.label i = a) :
    ∀ i j, g.label i = g.label j → i = j := by
  obtain ⟨a, ha⟩ := all .x
  obtain ⟨b, hb⟩ := all .y
  obtain ⟨c, hc⟩ := all .z
  cases a <;> cases b <;> cases c <;> (try simp_all) <;>
    intro i j h <;> cases i <;> cases j <;> simp_all

/-- With z fixed to false we can contract its vertex. A z-only cycle
    contracts to dead. -/
inductive Two where
  | x | y | result (b : Bool) | dead
  deriving DecidableEq

private def bare (g : Graph Site) : State Site → Two
  | .query i => match g.label i with
    | .x => .x
    | .y => .y
    | .z => .dead
  | .result b => .result b
  | .dead => .dead

private def contract (g : Graph Site) (iz : Site) : State Site → Two
  | .query i => if g.label i = .z then bare g (g.edge iz false) else bare g (.query i)
  | .result b => .result b
  | .dead => .dead

private theorem dropZ {g : Graph Site} {iz : Site}
    (hz : g.label iz = .z) (uniq : ∀ i j, g.label i = g.label j → i = j) :
    contract g iz (.query iz) = contract g iz (g.edge iz false) := by
  cases he : g.edge iz false with
  | result v => simp [contract, bare, hz, he]
  | dead => simp [contract, bare, hz, he]
  | query j =>
    by_cases hj : g.label j = .z
    · have eq := uniq j iz (hj.trans hz.symm)
      subst j
      simp [contract, bare, hz]
    · simp [contract, bare, he, hz, hj]

private def readout (a b : Two) : Nat → Two → Option Bool
  | 0, .result answer => some answer
  | 0, _ => none
  | k+1, .x => readout a b k a
  | k+1, .y => readout a b k b
  | _+1, .result answer => some answer
  | _+1, .dead => none

private theorem twoEnough (a b q : Two) (k : Nat) (v : Bool)
    (h : readout a b k q = some v) : readout a b 2 q = some v := by
  induction k generalizing q with
  | zero => cases q <;> simp_all [readout]
  | succ k ih =>
    cases q with
    | result c => exact h
    | dead => exact h
    | x =>
      have prev := ih a h
      have stable : readout a b 2 a = readout a b 1 a := by
        cases a <;> cases b <;> rfl
      exact stable.symm.trans prev
    | y =>
      have prev := ih b h
      have stable : readout a b 2 b = readout a b 1 b := by
        cases a <;> cases b <;> rfl
      exact stable.symm.trans prev

private def xy (u v : Bool) : Input
  | .x => u
  | .y => v
  | .z => false

private theorem projectHalt {g : Graph Site} {ix iy iz : Site}
    (hx : g.label ix = .x) (hy : g.label iy = .y) (hz : g.label iz = .z)
    (uniq : ∀ i j, g.label i = g.label j → i = j) {u v answer : Bool} {q : State Site}
    (h : Halts g (xy u v) q answer) :
    ∃ k, readout (contract g iz (g.edge ix u)) (contract g iz (g.edge iy v))
      k (contract g iz q) = some answer := by
  induction h with
  | result => exact ⟨0, rfl⟩
  | @query j answer _ ih =>
    obtain ⟨k, hk⟩ := ih
    cases hj : g.label j with
    | x =>
      have eq := uniq j ix (hj.trans hx.symm)
      subst j
      exact ⟨k+1, by simpa [contract, bare, hx, xy, readout] using hk⟩
    | y =>
      have eq := uniq j iy (hj.trans hy.symm)
      subst j
      exact ⟨k+1, by simpa [contract, bare, hy, xy, readout] using hk⟩
    | z =>
      have eq := uniq j iz (hj.trans hz.symm)
      subst j
      exact ⟨k, by rw [dropZ hz uniq]; simpa only [hz, xy] using hk⟩

private def decode : Fin 5 → Two
  | 0 => .x
  | 1 => .y
  | 2 => .result false
  | 3 => .result true
  | 4 => .dead

private theorem encoded (q : Two) : ∃ i, decode i = q := by
  cases q with
  | x => exact ⟨0, rfl⟩
  | y => exact ⟨1, rfl⟩
  | result v => cases v <;> first | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
  | dead => exact ⟨4, rfl⟩

private theorem twoCannot (q a a' b b' : Two) :
    ¬ (readout a b 2 q = some true ∧ readout a b' 2 q = some false ∧
       readout a' b 2 q = some false ∧ readout a' b' 2 q = some true) := by
  obtain ⟨iq, rfl⟩ := encoded q
  obtain ⟨ia, rfl⟩ := encoded a
  obtain ⟨ia', rfl⟩ := encoded a'
  obtain ⟨ib, rfl⟩ := encoded b
  obtain ⟨ib', rfl⟩ := encoded b'
  have all : ∀ s i j k l : Fin 5,
    ¬ (readout (decode i) (decode k) 2 (decode s) = some true ∧
       readout (decode i) (decode l) 2 (decode s) = some false ∧
       readout (decode j) (decode k) 2 (decode s) = some false ∧
       readout (decode j) (decode l) 2 (decode s) = some true) := by decide
  exact all iq ia ia' ib ib'

/-- Three query vertices, with arbitrary input labels, start, edges and
    cycles, cannot decide the guarded equality table on all eight inputs. -/
theorem three_vertices_cannot_decide (g : Graph Site) :
    ¬ ∀ p, Halts g p g.start (target p) := by
  intro decides
  have all := allLabels decides
  have uniq := uniqueLabels all
  obtain ⟨ix, hx⟩ := all .x
  obtain ⟨iy, hy⟩ := all .y
  obtain ⟨iz, hz⟩ := all .z
  have checks (u v : Bool) := (projectHalt hx hy hz uniq (decides (xy u v))).elim
    (fun k hk => twoEnough _ _ _ k _ hk)
  exact twoCannot _ _ _ _ _
    ⟨checks false false, checks false true, checks true false, checks true true⟩

inductive Four where
  | guard | leftBit | rightIfZero | rightIfOne

/-- A program attaining four vertices tests z, then remembers x by choosing
    which of two y-vertices to enter. -/
def fourVertexProgram : Graph Four where
  start := .query .guard
  label
    | .guard => .z
    | .leftBit => .x
    | .rightIfZero | .rightIfOne => .y
  edge
    | .guard, true => .result false
    | .guard, false => .query .leftBit
    | .leftBit, false => .query .rightIfZero
    | .leftBit, true => .query .rightIfOne
    | .rightIfZero, b => .result (!b)
    | .rightIfOne, b => .result b

theorem four_vertices_suffice (p : Input) :
    Halts fourVertexProgram p fourVertexProgram.start (target p) := by
  apply Halts.query
  cases hz : p .z <;> simp [fourVertexProgram, hz, target]
  · apply Halts.query
    cases hx : p .x <;> simp [hx] <;> apply Halts.query <;>
      cases hy : p .y <;> simp [hy] <;> exact Halts.result
  · exact Halts.result

end NestedQueryTable
