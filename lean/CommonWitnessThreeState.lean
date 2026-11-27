import Std

namespace CommonWitnessThreeState

/-- The two live states and one absorbing rejecting state. -/
inductive State where
  | live (bit : Bool)
  | dead
  deriving DecidableEq, Repr

def finish (ok : Bool) : State := if ok then .live false else .dead

/-- Each occurrence has a name and its required truth value (true for a positive literal). -/
structure Clause (O : Type) where
  enabled : Bool
  literals : List (O × Bool)

def signs (word : O → Bool) (c : Clause O) : List Bool :=
  c.literals.map (fun l => word l.1 == l.2)

def clauseOK (word : O → Bool) (c : Clause O) : Bool :=
  !c.enabled || (signs word c).any id

def resetLive : State → State
  | .live _ => .live false
  | .dead => .dead

def literalStep : State → Bool → State
  | .live seen, b => .live (seen || b)
  | .dead, _ => .dead

def closeClause (enabled : Bool) : State → State
  | .live seen => finish (!enabled || seen)
  | .dead => .dead

private theorem scanLiterals_live (bits : List Bool) (seen : Bool) :
    bits.foldl literalStep (.live seen) = .live (seen || bits.any id) := by
  induction bits generalizing seen with
  | nil => simp
  | cons b rest ih => simp [literalStep, ih, Bool.or_assoc]

private theorem scanLiterals_dead (bits : List Bool) :
    bits.foldl literalStep .dead = .dead := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [literalStep] using ih

/-- Every literal in the public row is queried, even in the rejecting state.
    Opening and closing the row are fixed transitions with no witness query. -/
def readClause (word : O → Bool) (c : Clause O) (s : State) : State :=
  closeClause c.enabled ((signs word c).foldl literalStep (resetLive s))

private theorem readClause_live (word : O → Bool) (c : Clause O) (b : Bool) :
    readClause word c (.live b) = finish (clauseOK word c) := by
  simp [readClause, resetLive, scanLiterals_live, closeClause, clauseOK]

private theorem readClause_dead (word : O → Bool) (c : Clause O) :
    readClause word c .dead = .dead := by
  simp [readClause, resetLive, scanLiterals_dead, closeClause]

/-- Every row or group boundary acts on the same three states. -/
def run (step : R → State → State) : List R → State → State
  | [], s => s
  | r :: rs, s => run step rs (step r s)

private theorem run_correct (step : R → State → State) (ok : R → Bool)
    (absorbs : ∀ r, step r .dead = .dead)
    (starts : ∀ r, step r (.live false) = finish (ok r)) (rs : List R) :
    (run step rs .dead = .dead) ∧
      (run step rs (.live false) = finish (rs.all ok)) := by
  induction rs with
  | nil => simp [run, finish]
  | cons r rs ih =>
    constructor
    · simp [run, absorbs, ih.1]
    · cases h : ok r <;> simp [run, starts, finish, h, ih.1, ih.2]

theorem clause_reader_correct (word : O → Bool) (rows : List (Clause O)) :
    run (readClause word) rows (.live false) = .live false ↔
      rows.all (clauseOK word) = true := by
  rw [(run_correct (readClause word) (clauseOK word) (readClause_dead word)
    (fun c => readClause_live word c false) rows).2]
  cases rows.all (clauseOK word) <;> simp [finish]

def firstInGroup : State → Bool → State
  | .live _, b => .live b
  | .dead, _ => .dead

def equalStep : State → Bool → State
  | .live first, b => if b == first then .live first else .dead
  | .dead, _ => .dead

private theorem scanEqual_dead (bits : List Bool) :
    bits.foldl equalStep .dead = .dead := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [equalStep] using ih

private theorem scanEqual_live (bits : List Bool) (first : Bool) :
    bits.foldl equalStep (.live first) =
      (if bits.all (fun b => b == first) then .live first else .dead) := by
  induction bits with
  | nil => simp
  | cons b rest ih =>
    by_cases h : b = first <;> simp [equalStep, h, ih, scanEqual_dead]

def groupOK (word : O → Bool) : List O → Bool
  | [] => true
  | a :: as => as.all (fun b => word b == word a)

/-- The first query stores the reference bit; each later query checks it.
    A group boundary resets the live state for the next group. -/
def readGroup (word : O → Bool) (group : List O) (s : State) : State :=
  match group with
  | [] => resetLive s
  | a :: as => resetLive ((as.map word).foldl equalStep (firstInGroup s (word a)))

private theorem readGroup_live (word : O → Bool) (g : List O) :
    readGroup word g (.live false) = finish (groupOK word g) := by
  cases g with
  | nil => rfl
  | cons a as =>
    simp only [readGroup, firstInGroup, scanEqual_live, List.all_map, Function.comp_def, groupOK]
    cases h : as.all (fun b => word b == word a) <;> simp [h, finish, resetLive]

private theorem readGroup_dead (word : O → Bool) (g : List O) :
    readGroup word g .dead = .dead := by
  cases g <;> simp [readGroup, resetLive, firstInGroup, scanEqual_dead]

theorem group_reader_correct (word : O → Bool) (gs : List (List O)) :
    run (readGroup word) gs (.live false) = .live false ↔
      ∀ g ∈ gs, groupOK word g = true := by
  rw [(run_correct (readGroup word) (groupOK word) (readGroup_dead word)
    (readGroup_live word) gs).2, ← List.all_eq_true]
  cases gs.all (groupOK word) <;> simp [finish]

private theorem uniform_group (word : O → Bool) (g : List O) :
    groupOK word g = true ↔ ∀ a ∈ g, ∀ b ∈ g, word a = word b := by
  cases g with
  | nil => simp [groupOK]
  | cons a as =>
    simp only [groupOK, List.all_eq_true, beq_iff_eq]
    constructor
    · intro h x hx y hy
      have equal (z : O) (hz : z ∈ a :: as) : word z = word a := by
        rcases List.mem_cons.mp hz with rfl | hm
        · rfl
        · exact h z hm
      exact (equal x hx).trans (equal y hy).symm
    · intro h b hb
      exact h b (List.mem_cons_of_mem _ hb) a (by simp)

def occurrences (rows : List (Clause O)) : List O :=
  rows.flatMap (fun c => c.literals.map Prod.fst)

/-- The second reader queries whole wire groups in the supplied wire order. -/
def groupFor [DecidableEq W] (wire : O → W) (os : List O) (w : W) : List O :=
  os.filter (fun o => wire o == w)

def groups [DecidableEq W] (wire : O → W) (os : List O) (names : List W) : List (List O) :=
  names.map (groupFor wire os)

private theorem in_group [DecidableEq W] (wire : O → W) (os : List O) (w : W) (o : O) :
    o ∈ groupFor wire os w ↔ o ∈ os ∧ wire o = w := by
  simp [groupFor, List.mem_filter]

private theorem grouped_count [DecidableEq W] [DecidableEq O] (wire : O → W)
    (os : List O) (names : List W) (o : O) :
    ((groups wire os names).flatten).count o = names.count (wire o) * os.count o := by
  induction names with
  | nil => simp [groups]
  | cons w ws ih =>
    change ((groupFor wire os w) ++ (groups wire os ws).flatten).count o = _
    rw [List.count_append, ih, List.count_cons]
    by_cases h : wire o = w
    · subst w
      have inside : (groupFor wire os (wire o)).count o = os.count o :=
        List.count_filter (by simp)
      simp [inside, Nat.add_mul, Nat.add_comm]
    · have outside : o ∉ groupFor wire os w := fun hm => h ((in_group _ _ _ _).mp hm).2
      simp [List.count_eq_zero_of_not_mem outside, Ne.symm h]

private theorem count_one_of_nodup [DecidableEq W] (ws : List W) (w : W)
    (hn : ws.Nodup) (hw : w ∈ ws) : ws.count w = 1 := by
  induction ws with
  | nil => simp at hw
  | cons j js ih =>
    rcases List.nodup_cons.mp hn with ⟨hmiss, htail⟩
    rcases List.mem_cons.mp hw with he | hmem
    · subst j
      simp [List.count_cons, List.count_eq_zero_of_not_mem hmiss]
    · have hne : j ≠ w := fun e => hmiss (e ▸ hmem)
      simp [List.count_cons, ih htail hmem, hne]

/-- The two actual occurrence orders are permutations. Hence when the first uses
    fresh occurrence IDs, the second reads each of them exactly once as well. -/
theorem read_orders_perm [DecidableEq O] [DecidableEq W] (wire : O → W)
    (os : List O) (names : List W) (uniqueNames : names.Nodup)
    (cover : ∀ o ∈ os, wire o ∈ names) : (groups wire os names).flatten.Perm os := by
  apply List.perm_iff_count.mpr
  intro o
  rw [grouped_count]
  by_cases ho : o ∈ os
  · simp [count_one_of_nodup names (wire o) uniqueNames (cover o ho)]
  · simp [List.count_eq_zero_of_not_mem ho]

theorem groups_read_once [DecidableEq O] [DecidableEq W] (rows : List (Clause O))
    (wire : O → W) (names : List W) (names_once : names.Nodup)
    (cover : ∀ o ∈ occurrences rows, wire o ∈ names) (fresh : (occurrences rows).Nodup) :
    (groups wire (occurrences rows) names).flatten.Nodup :=
  (read_orders_perm wire (occurrences rows) names names_once cover).symm.nodup fresh

private theorem in_occurrences {rows : List (Clause O)} {c : Clause O} {l : O × Bool}
    (hc : c ∈ rows) (hl : l ∈ c.literals) : l.1 ∈ occurrences rows := by
  exact List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

private theorem agree_on_rows {rows : List (Clause O)} {x y : O → Bool}
    (agree : ∀ o ∈ occurrences rows, x o = y o) :
    rows.all (clauseOK x) = rows.all (clauseOK y) := by
  have each (c : Clause O) (hc : c ∈ rows) : clauseOK x c = clauseOK y c := by
    have he : signs x c = signs y c := by
      apply List.map_congr_left
      intro l hl
      simp [agree l.1 (in_occurrences hc hl)]
    simp [clauseOK, he]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h c hc
    rw [← each c hc]
    exact h c hc
  · intro h c hc
    rw [each c hc]
    exact h c hc

/-- Joint acceptance of both complete readers is equivalent to SAT of the
    original clauses, which are interpreted on the original wires.
    Disabled rows are true even when empty. Enabled empty rows reject. -/
theorem common_witness_iff [DecidableEq W] (rows : List (Clause O)) (wire : O → W)
    (names : List W) (cover : ∀ o ∈ occurrences rows, wire o ∈ names) :
    (∃ word : O → Bool,
      run (readClause word) rows (.live false) = .live false ∧
      run (readGroup word) (groups wire (occurrences rows) names) (.live false) = .live false) ↔
    ∃ assignment : W → Bool, rows.all (clauseOK (assignment ∘ wire)) = true := by
  classical
  constructor
  · rintro ⟨word, hr, hg⟩
    let assignment : W → Bool := fun w =>
      ((groupFor wire (occurrences rows) w).any word)
    have agree (o : O) (ho : o ∈ occurrences rows) : word o = assignment (wire o) := by
      let g := groupFor wire (occurrences rows) (wire o)
      have hgmem : g ∈ groups wire (occurrences rows) names :=
        List.mem_map.mpr ⟨wire o, cover o ho, rfl⟩
      have hok := (uniform_group word g).mp ((group_reader_correct _ _).mp hg g hgmem)
      have hmem : o ∈ g := (in_group _ _ _ _).mpr ⟨ho, rfl⟩
      change word o = g.any word
      cases h : word o with
      | true => exact (List.any_eq_true.mpr ⟨o, hmem, h⟩).symm
      | false =>
        cases ha : g.any word with
        | false => rfl
        | true =>
          obtain ⟨b, hb, hv⟩ := List.any_eq_true.mp ha
          have := hok b hb o hmem
          simp_all
    refine ⟨assignment, ?_⟩
    rw [← agree_on_rows (x := word) (y := assignment ∘ wire) agree]
    exact (clause_reader_correct _ _).mp hr
  · rintro ⟨assignment, hs⟩
    refine ⟨assignment ∘ wire, (clause_reader_correct _ _).mpr hs, (group_reader_correct _ _).mpr ?_⟩
    intro g hg
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
    apply (uniform_group _ _).mpr
    intro a ha b hb
    simp [Function.comp_def, ((in_group _ _ _ _).mp ha).2, ((in_group _ _ _ _).mp hb).2]

end CommonWitnessThreeState
