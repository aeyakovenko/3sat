import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! An explicit sequence of individual port transpositions on arbitrary signed
NAE rows and arbitrary sheet counts. A pair uses sheet indices 0 and 1 inside
its block. A triple additionally uses 2. All blocks use the same assignment
on indices 0 and 2 and its complement on 1. -/

namespace SatCoverOptimality

abbrev Port := Fin 3
abbrev Slot := Fin 3
abbrev Row := Bool × Bool × Bool

def atPort (r : Row) (p : Port) : Bool :=
  if p = 0 then r.1 else if p = 1 then r.2.1 else r.2.2

def mono (r : Row) : Bool := (r.1 == r.2.1) && (r.1 == r.2.2)

def arity (triple : Bool) : Nat := if triple then 3 else 2

structure Switch where
  sign : Bool
  port : Port
  first : Slot
  second : Slot
  deriving DecidableEq

/-- Endpoint sheet of a specified signed-clause occurrence. -/
abbrev Wiring := Bool → Port → Slot → Slot

def straight : Wiring := fun _ _ sheet => sheet

def transpose (w : Wiring) (s : Switch) : Wiring := fun sign port sheet =>
  if sign = s.sign ∧ port = s.port then
    w sign port (if sheet = s.first then s.second else if sheet = s.second then s.first else sheet)
  else w sign port sheet

def holds (r : Row) (w : Wiring) (sign : Bool) (sheet : Slot) : Bool :=
  let read := fun p : Port => (atPort r p ^^ sign) ^^ decide (w sign p sheet = 1)
  read 0 || read 1 || read 2

def legal (triple : Bool) (s : Switch) : Prop :=
  s.first ≠ s.second ∧ s.first.val < arity triple ∧ s.second.val < arity triple

def plan (r : Row) (triple : Bool) : List Switch :=
  if mono r then
    [⟨false, 0, 0, 1⟩, ⟨true, 0, 0, 1⟩] ++
      (if triple then [⟨r.1, 1, 1, 2⟩] else [])
  else []

theorem local_count (r : Row) (triple : Bool) :
    (plan r triple).length = (mono r).toNat * arity triple := by
  obtain ⟨a,b,c⟩ := r
  cases a <;> cases b <;> cases c <;> cases triple <;> decide

theorem local_legal (r : Row) (triple : Bool) :
    ∀ s ∈ plan r triple, legal triple s := by
  obtain ⟨a,b,c⟩ := r
  cases a <;> cases b <;> cases c <;> cases triple <;>
    simp [plan, mono, legal, arity]

theorem local_sat (r : Row) (triple sign : Bool) :
    ∀ slot : Slot, slot.val < arity triple →
      holds r ((plan r triple).foldl transpose straight) sign slot = true := by
  obtain ⟨a,b,c⟩ := r
  cases a <;> cases b <;> cases c <;> cases triple <;> cases sign <;> decide

section Schedule

variable {I : Type*} [DecidableEq I]

def atTile (walk : List (I × Switch)) (i : I) : List Switch :=
  walk.filterMap (fun step => if step.1 = i then some step.2 else none)

def schedule (tiles : List I) (actions : I → List Switch) : List (I × Switch) :=
  tiles.flatMap fun i => (actions i).map (fun a => (i,a))

theorem schedule_projection (i : I) (tiles : List I) (actions : I → List Switch)
    (hn : tiles.Nodup) :
    atTile (schedule tiles actions) i = if i ∈ tiles then actions i else [] := by
  induction tiles with
  | nil => simp [atTile, schedule]
  | cons x xs ih =>
    rw [List.nodup_cons] at hn
    have ih' := ih hn.2
    simp only [atTile] at ih' ⊢
    simp only [schedule, List.flatMap_cons, List.filterMap_append, List.filterMap_map,
      Function.comp_def] at ih' ⊢
    by_cases hx : x = i
    · subst x
      simp [hn.1, ih']
    · simp [hx, Ne.symm hx, ih']

end Schedule

def isTriple {pairs triples : Nat} (b : Fin pairs ⊕ Fin triples) : Bool :=
  b.elim (fun _ => false) (fun _ => true)

/-- A grid cell of this table consists of one signed pair of clauses on one
block of two or three sheets. A global walk is an ordered list with one
specific grid cell and one endpoint transposition per step. -/
theorem repair_grid {C B : Type*} [Fintype C] [Fintype B] [DecidableEq C] [DecidableEq B]
    (rows : C → Row) (triple : B → Bool) :
    ∃ walk : List ((C × B) × Switch),
      walk.length = (∑ b, arity (triple b)) * ∑ c, (mono (rows c)).toNat ∧
      (∀ step ∈ walk, legal (triple step.1.2) step.2) ∧
      ∀ c b sign slot, slot.val < arity (triple b) →
        holds (rows c) ((atTile walk (c,b)).foldl transpose straight) sign slot = true := by
  classical
  let cells := (Finset.univ : Finset (C × B)).toList
  let actions := fun i : C × B => plan (rows i.1) (triple i.2)
  refine ⟨schedule cells actions, ?_, ?_, ?_⟩
  · rw [schedule, List.length_flatMap]
    simp only [List.length_map, cells, Finset.sum_map_toList, actions, local_count]
    rw [Fintype.sum_prod_type, Nat.mul_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  · intro step hstep
    obtain ⟨i, _, htag⟩ := List.mem_flatMap.mp hstep
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp htag
    exact local_legal (rows i.1) (triple i.2) s hs
  · intro c b sign slot hs
    have hin : (c,b) ∈ cells := by simp [cells]
    have hproj := schedule_projection (c,b) cells actions (Finset.nodup_toList _)
    simp [hin] at hproj
    rw [hproj]
    exact local_sat (rows c) (triple b) sign slot hs

/-- Closed form at every sheet count of at least two. The returned pair
and triple counts specify exactly d real sheets. -/
theorem repair_at_every_degree {C : Type*} [Fintype C] [DecidableEq C]
    (rows : C → Row) (d : Nat) (hd : 2 ≤ d) :
    ∃ p t : Nat, 2*p+3*t=d ∧ t ≤ 1 ∧
      ∃ walk : List ((C × (Fin p ⊕ Fin t)) × Switch),
        walk.length = d * ∑ c, (mono (rows c)).toNat ∧
        (∀ step ∈ walk, legal (isTriple step.1.2) step.2) ∧
        ∀ c b sign (slot : Slot), slot.val < arity (isTriple b) →
          holds (rows c) ((atTile walk (c,b)).foldl transpose straight) sign slot = true := by
  obtain ⟨p,t,hd',ht⟩ : ∃ p t : Nat, 2*p+3*t=d ∧ t ≤ 1 := by
    by_cases h : d % 2 = 0
    · exact ⟨d / 2, 0, by omega, by omega⟩
    · exact ⟨(d-3)/2, 1, by omega, by omega⟩
  obtain ⟨walk,len,valid,satisfied⟩ :=
    repair_grid rows (isTriple (pairs := p) (triples := t))
  have sz : (∑ b : Fin p ⊕ Fin t, arity (isTriple b)) = d := by
    rw [Fintype.sum_sum_type]
    simp [arity, isTriple, Nat.mul_comm, ← hd']
  exact ⟨p,t,hd',ht,walk,sz ▸ len,valid,satisfied⟩

/-- A literal stores its variable and the bit indicating negation. -/
abbrev SignedRow (V : Type*) := Port → V × Bool

def atAssignment {V : Type*} (r : SignedRow V) (a : V → Bool) (port : Port) : Bool :=
  a (r port).1 ^^ (r port).2

def rowValues {V : Type*} (r : SignedRow V) (a : V → Bool) : Row :=
  (atAssignment r a 0, atAssignment r a 1, atAssignment r a 2)

def liftedClause {V : Type*} (r : SignedRow V) (a : V → Bool) (w : Wiring)
    (sign : Bool) (slot : Slot) : Bool :=
  let read := fun port : Port =>
    let endpoint := w sign port slot
    let varName := (r port).1
    let value := if endpoint = 1 then !(a varName) else a varName
    (value ^^ (r port).2) ^^ sign
  read 0 || read 1 || read 2

theorem lifted_clause_semantics {V : Type*} (r : SignedRow V) (a : V → Bool)
    (w : Wiring) (sign : Bool) (slot : Slot) :
    liftedClause r a w sign slot = holds (rowValues r a) w sign slot := by
  have same (x neg : Bool) (j : Slot) :
      (((if j = 1 then !x else x) ^^ neg) ^^ sign) =
      (((x ^^ neg) ^^ sign) ^^ decide (j = 1)) := by
    by_cases hj : j = 1 <;> cases x <;> cases neg <;> cases sign <;> simp [hj]
  simp only [liftedClause, holds, same]
  rfl

/-- The satisfying values here come from one common assignment on the base
variables and its complement across sheets. Repeated names or literals do not
require independence. Use a minimizing assignment to obtain the du bound. -/
theorem repair_signed_instance {C V : Type*} [Fintype C] [DecidableEq C]
    (formula : C → SignedRow V) (a : V → Bool) (d : Nat) (hd : 2 ≤ d) :
    ∃ p t : Nat, 2*p+3*t=d ∧ t ≤ 1 ∧
      ∃ walk : List ((C × (Fin p ⊕ Fin t)) × Switch),
        walk.length = d * ∑ c, (mono (rowValues (formula c) a)).toNat ∧
        (∀ step ∈ walk, legal (isTriple step.1.2) step.2) ∧
        ∀ c b sign (slot : Slot), slot.val < arity (isTriple b) →
          liftedClause (formula c) a ((atTile walk (c,b)).foldl transpose straight)
            sign slot = true := by
  simpa only [lifted_clause_semantics] using
    repair_at_every_degree (fun c => rowValues (formula c) a) d hd

/-- The two rows of a general switch need only agree in base clause and sign.
Their sheets can lie in entirely different repair blocks. -/
structure Move (S C : Type*) where
  clause : C
  sign : Bool
  port : Port
  first : S
  second : S

abbrev Location (S C : Type*) := S × C × Bool

def leftEnd {S C} (m : Move S C) : Location S C := (m.first, m.clause, m.sign)

def rightEnd {S C} (m : Move S C) : Location S C := (m.second, m.clause, m.sign)

abbrev Table (S C A : Type*) := Location S C → Port → A

/-- The value type can be an endpoint, or its truth on a fixed assignment. -/
def act {S C A} [DecidableEq S] [DecidableEq C] (tab : Table S C A)
    (m : Move S C) : Table S C A := fun e p =>
  if p = m.port then
    if e = leftEnd m then tab (rightEnd m) p
    else if e = rightEnd m then tab (leftEnd m) p
    else tab e p
  else tab e p

def defect (bits : Port → Bool) : Nat :=
  if bits 0 || bits 1 || bits 2 then 0 else 1

theorem defect_mono {x y : Port → Bool}
    (h : ∀ p, y p = true → x p = true) : defect x ≤ defect y := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  cases h0' : x 0 <;> cases h1' : x 1 <;> cases h2' : x 2 <;>
    simp_all [defect]
  have y0 : y 0 ≠ true := fun hy => Bool.noConfusion (h0'.symm.trans (h 0 hy))
  have y1 : y 1 ≠ true := fun hy => Bool.noConfusion (h1'.symm.trans (h 1 hy))
  have y2 : y 2 ≠ true := fun hy => Bool.noConfusion (h2'.symm.trans (h 2 hy))
  simp [y0,y1,y2]

def localLoss {S C} (real : S → Bool) (tab : Table S C Bool) (j : Location S C) : Nat :=
  if real j.1 then defect (tab j) else 0

def totalLoss {S C} [Fintype S] [Fintype C] (real : S → Bool)
    (tab : Table S C Bool) : Nat := ∑ j, localLoss real tab j

theorem global_drop {S C} [Fintype S] [Fintype C] [DecidableEq S] [DecidableEq C]
    (real : S → Bool) (tab : Table S C Bool) (m : Move S C) :
    totalLoss real tab ≤ totalLoss real (act tab m) + 1 := by
  classical
  let risk := if tab (leftEnd m) m.port then rightEnd m else leftEnd m
  have point (j : Location S C) :
      localLoss real tab j ≤ localLoss real (act tab m) j + if j = risk then 1 else 0 := by
    by_cases hj : j = risk
    · have hlow : localLoss real tab j ≤ 1 := by
        simp only [localLoss, defect]
        split
        · split <;> decide
        · decide
      rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]
      omega
    · simp only [hj, ↓reduceIte, Nat.add_zero, localLoss]
      split
      · apply defect_mono
        intro p hy
        by_cases hp : p = m.port
        · subst p
          by_cases hl : j = leftEnd m
          · subst j
            cases hbit : tab (leftEnd m) m.port
            · exact False.elim (hj (by simp [risk, hbit]))
            · rfl
          · by_cases hr : j = rightEnd m
            · subst j
              cases hbit : tab (leftEnd m) m.port
              · simp [act, hl, hbit] at hy
              · exact False.elim (hj (by simp [risk, hbit]))
            · simpa [act,hl,hr] using hy
        · simpa [act,hp] using hy
      · exact Nat.le_refl _
  calc
    totalLoss real tab ≤ ∑ j : Location S C,
        (localLoss real (act tab m) j + if j = risk then 1 else 0) :=
      Finset.sum_le_sum (fun j _ => point j)
    _ = totalLoss real (act tab m) + 1 := by
      simp [Finset.sum_add_distrib, totalLoss]

theorem full_path_drop {S C} [Fintype S] [Fintype C] [DecidableEq S] [DecidableEq C]
    (real : S → Bool) (tab : Table S C Bool) (walk : List (Move S C)) :
    totalLoss real tab ≤ totalLoss real (walk.foldl act tab) + walk.length := by
  induction walk generalizing tab with
  | nil => simp
  | cons m ms ih =>
    have first := global_drop real tab m
    have rest := ih (act tab m)
    simp only [List.foldl_cons, List.length_cons]
    omega

def initialTruth {S C V} (formula : C → SignedRow V) (assignment : S → V → Bool) :
    Table S C Bool := fun e p =>
  (atAssignment (formula e.2.1) (assignment e.1) p) ^^ e.2.2

theorem signed_defect_sum (r : SignedRow V) (a : V → Bool) :
    (∑ sg : Bool, defect (fun p => atAssignment r a p ^^ sg)) =
      (mono (rowValues r a)).toNat := by
  rw [Fintype.sum_bool]
  cases h0 : atAssignment r a 0 <;> cases h1 : atAssignment r a 1 <;>
    cases h2 : atAssignment r a 2 <;> simp [defect, mono, rowValues, h0,h1,h2]

theorem initial_lower {S C V} [Fintype S] [Fintype C] (real : S → Bool)
    (formula : C → SignedRow V) (assignment : S → V → Bool) (u : Nat)
    (optimal : ∀ a : V → Bool, u ≤ ∑ c, (mono (rowValues (formula c) a)).toNat) :
    ((∑ s : S, (real s).toNat) * u) ≤ totalLoss real (initialTruth formula assignment) := by
  classical
  rw [Finset.sum_mul]
  unfold totalLoss
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro s _
  rw [Fintype.sum_prod_type]
  cases hs : real s
  · simp [localLoss, hs]
  · simp only [Bool.toNat_true, Nat.one_mul, localLoss, hs, ↓reduceIte]
    change u ≤ ∑ c : C, ∑ sg : Bool, defect (fun p => atAssignment (formula c) (assignment s) p ^^ sg)
    simp only [signed_defect_sum]
    exact optimal (assignment s)

theorem successful_path_lower {S C V} [Fintype S] [Fintype C] [DecidableEq S] [DecidableEq C]
    (real : S → Bool) (formula : C → SignedRow V) (u : Nat)
    (optimal : ∀ a : V → Bool, u ≤ ∑ c, (mono (rowValues (formula c) a)).toNat)
    (walk : List (Move S C)) (assignment : S → V → Bool)
    (sat : totalLoss real (walk.foldl act (initialTruth formula assignment)) = 0) :
    ((∑ s : S, (real s).toNat) * u) ≤ walk.length := by
  have start := initial_lower real formula assignment u optimal
  have bound := full_path_drop real (initialTruth formula assignment) walk
  omega


/-- Embed the sequence whose steps stay inside one block in the unrestricted
switch domain. The latter domain permits any two distinct active sheets. -/
def embed {C B} (k : (C × B) × Switch) : Move (B × Slot) C :=
  ⟨k.1.1, k.2.sign, k.2.port, (k.1.2,k.2.first), (k.1.2,k.2.second)⟩

def permuteSlot (move : Switch) (sg : Bool) (p : Port) (s : Slot) : Slot :=
  transpose straight move sg p s

theorem compose_slot (w : Wiring) (m : Switch) (sg : Bool) (p : Port) (s : Slot) :
    transpose w m sg p s = w sg p (permuteSlot m sg p s) := by
  by_cases h : sg = m.sign ∧ p = m.port <;> simp [transpose, permuteSlot, straight, h]

theorem embedded_step {C B A} [DecidableEq C] [DecidableEq B]
    (tab : Table (B × Slot) C A) (step : (C × B) × Switch)
    (c : C) (b : B) (sg : Bool) (p : Port) (s : Slot) :
    act tab (embed step) ((b,s),c,sg) p =
      tab ((b, if step.1 = (c,b) then permuteSlot step.2 sg p s else s),c,sg) p := by
  obtain ⟨⟨c',b'⟩,m⟩ := step
  by_cases hc : c = c' <;> by_cases hb : b = b' <;> by_cases hs : sg = m.sign <;>
    by_cases hp : p = m.port <;>
    simp [act, embed, leftEnd, rightEnd, permuteSlot, transpose, straight, hc,hb,hs,hp,
      Ne.symm, eq_comm]
  split <;> (first | rfl | (split <;> rfl))

theorem projected_append {I} [DecidableEq I] (steps : List (I × Switch)) (x : I × Switch) (i : I) :
    atTile (steps ++ [x]) i =
    if x.1 = i then atTile steps i ++ [x.2] else atTile steps i := by
  by_cases h : x.1 = i <;> simp [atTile, h]

theorem embedding_acts {C B A} [DecidableEq C] [DecidableEq B]
    (initial : Table (B × Slot) C A) (steps : List ((C × B) × Switch)) :
    ∀ c b sg p s,
    ((steps.map embed).foldl act initial) ((b,s),c,sg) p =
      initial ((b,((atTile steps (c,b)).foldl transpose straight) sg p s),c,sg) p := by
  induction steps using List.reverseRecOn with
  | nil => intros; rfl
  | append_singleton steps step ih =>
    intro c b sg p s
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
      List.foldl_nil, embedded_step, projected_append]
    by_cases h : step.1 = (c,b)
    · simp only [h, ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil, compose_slot]
      exact ih _ _ _ _ _
    · simp only [h, ↓reduceIte]
      exact ih _ _ _ _ _


def inBlock {B} (triple : B → Bool) (s : B × Slot) : Bool :=
  decide (s.2.val < arity (triple s.1))

def sheetAssignment {B V : Type*} (a : V → Bool) (s : B × Slot) (v : V) : Bool :=
  if s.2 = 1 then !(a v) else a v

def validMove {S C} (real : S → Bool) (m : Move S C) : Prop :=
  m.first ≠ m.second ∧ real m.first = true ∧ real m.second = true

def solves {S C V} [Fintype S] [Fintype C] [DecidableEq S] [DecidableEq C]
    (real : S → Bool) (formula : C → SignedRow V) (walk : List (Move S C)) : Prop :=
  ∃ assignment : S → V → Bool, totalLoss real (walk.foldl act (initialTruth formula assignment)) = 0

theorem full_lift_satisfied {C B V} [Fintype C] [Fintype B] [DecidableEq C] [DecidableEq B]
    (formula : C → SignedRow V) (a : V → Bool) (triple : B → Bool)
    (steps : List ((C × B) × Switch))
    (sat : ∀ c b sg s, s.val < arity (triple b) →
      liftedClause (formula c) a ((atTile steps (c,b)).foldl transpose straight) sg s = true) :
    solves (inBlock triple) formula (steps.map embed) := by
  refine ⟨sheetAssignment a, Finset.sum_eq_zero (fun j _ => ?_)⟩
  obtain ⟨⟨b,s⟩,c,sg⟩ := j
  by_cases h : s.val < arity (triple b)
  · have hs := sat c b sg s h
    simp only [localLoss, inBlock, h, decide_true, ↓reduceIte, defect, embedding_acts]
    change (if liftedClause (formula c) a ((atTile steps (c,b)).foldl transpose straight) sg s
      then 0 else 1) = 0
    simp [hs]
  · simp [localLoss, inBlock, h]

theorem number_real_sheets (p t : Nat) :
    (∑ s : (Fin p ⊕ Fin t) × Slot, (inBlock isTriple s).toNat) = 2*p + 3*t := by
  have one (b : Bool) : (∑ s : Slot, (decide (s.val < arity b)).toNat) = arity b := by
    cases b <;> decide
  rw [Fintype.sum_prod_type]
  simp only [inBlock, one]
  rw [Fintype.sum_sum_type]
  simp [isTriple, arity, Nat.mul_comm]

/-- The minimum is over all sequences of signed-port transpositions between
distinct real sheets, including transpositions joining different blocks. One
common assignment on every variable of every sheet must satisfy the endpoint.
Both the achieving path and every competing path use the same transition act.
The inactive third index of a two-sheet block cannot be a legal endpoint. -/
theorem exact_minimum {C V : Type*} [Fintype C] [DecidableEq C]
    (formula : C → SignedRow V) (a : V → Bool) (u d : Nat) (hd : 2 ≤ d)
    (attained : (∑ c, (mono (rowValues (formula c) a)).toNat) = u)
    (optimal : ∀ b : V → Bool, u ≤ ∑ c, (mono (rowValues (formula c) b)).toNat) :
    ∃ p t : Nat, 2*p+3*t=d ∧ t ≤ 1 ∧
      ∃ best : List (Move ((Fin p ⊕ Fin t) × Slot) C),
        best.length = d*u ∧ (∀ m ∈ best, validMove (inBlock isTriple) m) ∧
        solves (inBlock isTriple) formula best ∧
        ∀ rival : List (Move ((Fin p ⊕ Fin t) × Slot) C),
          (∀ m ∈ rival, validMove (inBlock isTriple) m) →
          solves (inBlock isTriple) formula rival → best.length ≤ rival.length := by
  obtain ⟨p,t,hn,ht,steps,hlen,hvalid,hsat⟩ := repair_signed_instance formula a d hd
  have len : (steps.map embed).length = d*u := by simp [hlen,attained]
  refine ⟨p,t,hn,ht,steps.map embed,len,?_,full_lift_satisfied formula a _ steps hsat,?_⟩
  · intro m hm
    obtain ⟨step, hin, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hneq,h1,h2⟩ := hvalid step hin
    simp [validMove, inBlock, embed, hneq,h1,h2]
  · intro rival _ succeeds
    obtain ⟨b,zero⟩ := succeeds
    have lower := successful_path_lower (inBlock isTriple) formula u optimal rival b zero
    rwa [len, ← hn, ← number_real_sheets p t]

/-- The actual variable endpoint at a literal occurrence is determined by its
base variable and this table of endpoint sheet labels. -/
def identityEndpoints {S C} : Table S C S := fun j _ => j.1

def readEndpoints {S C V} (formula : C → SignedRow V) (a : S → V → Bool)
    (endpoints : Table S C S) : Table S C Bool := fun j p =>
  atAssignment (formula j.2.1) (a (endpoints j p)) p ^^ j.2.2

theorem read_after_act {S C V} [DecidableEq S] [DecidableEq C]
    (formula : C → SignedRow V) (a : S → V → Bool) (endpoints : Table S C S)
    (m : Move S C) :
    readEndpoints formula a (act endpoints m) = act (readEndpoints formula a endpoints) m := by
  funext j p
  by_cases hp : p = m.port <;> by_cases hl : j = leftEnd m <;> by_cases hr : j = rightEnd m <;>
    simp_all [readEndpoints, act, leftEnd, rightEnd]

theorem read_after_walk {S C V} [DecidableEq S] [DecidableEq C]
    (formula : C → SignedRow V) (a : S → V → Bool) (endpoints : Table S C S)
    (walk : List (Move S C)) :
    readEndpoints formula a (walk.foldl act endpoints) =
    walk.foldl act (readEndpoints formula a endpoints) := by
  induction walk generalizing endpoints with
  | nil => rfl
  | cons m ms ih => simp only [List.foldl_cons, ih, read_after_act]

theorem solves_iff_endpoint_satisfiable {S C V} [Fintype S] [Fintype C]
    [DecidableEq S] [DecidableEq C] (real : S → Bool) (formula : C → SignedRow V)
    (walk : List (Move S C)) :
    solves real formula walk ↔
      ∃ a : S → V → Bool,
        totalLoss real (readEndpoints formula a (walk.foldl act identityEndpoints)) = 0 := by
  simp only [read_after_walk]
  rfl

/-- On a path attaining the global one-per-move lower bound, the fixed final
assignment witnesses the exact residual loss at every prefix. -/
theorem sharp_prefix {S C} [Fintype S] [Fintype C] [DecidableEq S] [DecidableEq C]
    (real : S → Bool) (initial : Table S C Bool) (before suffix : List (Move S C))
    (start : before.length + suffix.length ≤ totalLoss real initial)
    (finish : totalLoss real ((before ++ suffix).foldl act initial) = 0) :
    totalLoss real (before.foldl act initial) = suffix.length := by
  have first := full_path_drop real initial before
  have last := full_path_drop real (before.foldl act initial) suffix
  rw [List.foldl_append] at finish
  omega

#print axioms sharp_prefix
#print axioms solves_iff_endpoint_satisfiable

#print axioms global_drop
#print axioms exact_minimum



#print axioms repair_at_every_degree
#print axioms repair_signed_instance

end SatCoverOptimality
