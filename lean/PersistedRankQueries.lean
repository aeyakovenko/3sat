import Std

namespace PersistedRankQueries

/-- One attempted prefix position in a single preannounced schedule. After a
    cheap snapshot has been found its remaining allotted queries may be dummies. -/
structure Panel (α : Type) where
  prefixId : α
  costs : List Nat
  saved : Bool

def positions (panels : List (Panel α)) := panels.map Panel.prefixId
def lost (panels : List (Panel α)) := positions (panels.filter (fun p => !p.saved))
def kept (panels : List (Panel α)) := positions (panels.filter Panel.saved)
def spent (panels : List (Panel α)) := (panels.map (fun p => p.costs.sum)).sum

def AtQuota (K quota : Nat) (panels : List (Panel α)) : Prop :=
  ∀ p ∈ panels, p.costs.length = quota ∧
    (p.saved = false → ∀ c ∈ p.costs, K ≤ c)

/-- Rounding M/p up, with one harmless extra query when divisible, keeps
    total allotted slots between M and M+p inclusive. -/
theorem fixedQuota (M p : Nat) (positive : 0 < p) :
    M ≤ p * (M/p+1) ∧ p * (M/p+1) ≤ M+p := by
  have div := Nat.div_add_mod M p
  have rem := Nat.mod_lt M positive
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem costsLower (cs : List Nat) (K : Nat) (slow : ∀ c ∈ cs, K ≤ c) :
    cs.length*K ≤ cs.sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have first := slow c (.head _)
    have tail := ih (fun x hx => slow x (.tail c hx))
    simp only [List.length_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem failedCost (panels : List (Panel α)) (rule : AtQuota K q panels) :
    (lost panels).length*(q*K) ≤ spent panels := by
  induction panels with
  | nil => simp [lost,positions,spent]
  | cons p rest ih =>
    have first := rule p (.head _)
    have tail := ih (fun x hx => rule x (.tail _ hx))
    cases hs : p.saved with
    | false =>
      have cost := costsLower p.costs K (first.2 hs)
      rw [first.1] at cost
      change _ ≤ p.costs.sum+spent rest
      simpa [lost,positions,hs,Nat.add_mul,Nat.add_comm] using Nat.add_le_add cost tail
    | true =>
      change _ ≤ p.costs.sum+spent rest
      simpa [lost,positions,hs] using Nat.le_trans tail (Nat.le_add_left _ p.costs.sum)

/-- If all work is amortized against M setup and exactly |P|q queries,
    doubling each failed prefix's minimum cost still fits the full quota's
    budget at threshold 4C. This charges the *same actual run* once. -/
theorem fixedScheduleHalves (panels : List (Panel α)) (M C q : Nat)
    (positiveC : 0 < C) (positiveQ : 0 < q)
    (full : M ≤ panels.length*q)
    (cost : spent panels ≤ C*(M+panels.length*q))
    (rule : AtQuota (4*C) q panels) :
    2*(lost panels).length ≤ (positions panels).length := by
  have bad := failedCost panels rule
  have up := Nat.mul_le_mul_left C (Nat.add_le_add_right full (panels.length*q))
  have twice := Nat.mul_le_mul_left 2 (Nat.le_trans bad (Nat.le_trans cost up))
  have right : 2*(C*(panels.length*q+panels.length*q)) = panels.length*(q*(4*C)) := by
    rw [←Nat.two_mul]
    change 2*(C*(2*(panels.length*q))) = panels.length*(q*((2*2)*C))
    ac_rfl
  rw [right, ←Nat.mul_assoc] at twice
  have nz : 0 < q*(4*C) := Nat.mul_pos positiveQ (Nat.mul_pos (by decide) positiveC)
  simpa [positions] using Nat.le_of_mul_le_mul_right twice nz

/-- A fresh schedule receives exactly the previously unresolved positions.
    Its numerical cost and the threshold tests are explicit for each round. -/
inductive Rounds (α : Type) : Nat → List α → List α → List α → Prop where
  | done (xs : List α) : Rounds α 0 xs xs []
  | next {n : Nat} {remaining records : List α} (panels : List (Panel α)) (M C q : Nat)
      (positiveC : 0 < C) (positiveQ : 0 < q) (full : M ≤ panels.length*q)
      (cost : spent panels ≤ C*(M+panels.length*q)) (rule : AtQuota (4*C) q panels)
      (later : Rounds α n (lost panels) remaining records) :
      Rounds α (n+1) (positions panels) remaining (kept panels ++ records)

private theorem splitPanel (panels : List (Panel α)) (v : α) (member : v ∈ positions panels) :
    v ∈ lost panels ∨ v ∈ kept panels := by
  obtain ⟨p,hp,val⟩ := List.mem_map.mp member
  cases hs : p.saved with
  | false =>
    left
    exact val ▸ List.mem_map_of_mem (List.mem_filter.mpr ⟨hp,by simp [hs]⟩)
  | true =>
    right
    exact val ▸ List.mem_map_of_mem (List.mem_filter.mpr ⟨hp,hs⟩)

theorem roundsPay (runs : Rounds α n initial remaining records) :
    2^n * remaining.length ≤ initial.length ∧
    ∀ p ∈ initial, p ∈ remaining ∨ p ∈ records := by
  induction runs with
  | done xs => exact ⟨by simp, fun p hp => Or.inl hp⟩
  | next panels M C q pc pq full cost rule later ih =>
    have half := fixedScheduleHalves panels M C q pc pq full cost rule
    constructor
    · have twice := Nat.mul_le_mul_left 2 ih.1
      rw [Nat.pow_succ', Nat.mul_assoc]
      exact Nat.le_trans twice half
    · intro p hp
      rcases splitPanel panels p hp with lostNow | savedNow
      · rcases ih.2 p lostNow with still | found
        · exact Or.inl still
        · exact Or.inr (List.mem_append_right _ found)
      · exact Or.inr (List.mem_append_left _ savedNow)

theorem allSnapshots (runs : Rounds α n initial remaining records)
    (enough : initial.length < 2^n) :
    remaining = [] ∧ ∀ p ∈ initial, p ∈ records := by
  obtain ⟨paid,covers⟩ := roundsPay runs
  cases remaining with
  | nil => exact ⟨rfl,fun p hp => (covers p hp).resolve_left (List.not_mem_nil)⟩
  | cons head rest =>
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at paid
    omega

/-- Change only one addressed physical word per event. The snapshot query
    below consumes the first n events, where n is a time just before the
    next operation. All other addresses retain their incoming values. -/
def replayAt [DecidableEq A] (address : A) (initial : V) :
    Nat → List (A × V) → V
  | 0, _ => initial
  | _+1, [] => initial
  | n+1, (a,v) :: rest => replayAt address (if a = address then v else initial) n rest

/-- Complete timestamped write history for one address; timestamps strictly
    increase, and an unmodified address has an empty history. -/
def history [DecidableEq A] (address : A) (time : Nat) : List (A × V) → List (Nat × V)
  | [] => []
  | (a,v) :: rest =>
    if a = address then (time+1,v) :: history address (time+1) rest
    else history address (time+1) rest

def before (cut : Nat) (initial : V) : List (Nat × V) → V
  | [] => initial
  | (time,v) :: past => if time ≤ cut then before cut v past else initial

private theorem untouched [DecidableEq A] (ops : List (A × V)) (a : A) (t cut : Nat)
    (v : V) (past : cut ≤ t) : before cut v (history a t ops) = v := by
  induction ops generalizing t with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨k,x⟩ := op
    by_cases hit : k = a
    · have future : ¬ t+1 ≤ cut := by omega
      simp [history,hit,before,future]
    · simpa [history,hit] using ih (t+1) (by omega)

/-- Predecessor restoration computes the actual historical response even
    for repeated writes and sparse addresses. -/
theorem historicalRead [DecidableEq A] (ops : List (A × V)) (a : A) (t n : Nat)
    (initial : V) :
    before (t+n) initial (history a t ops) = replayAt a initial n ops := by
  induction ops generalizing t n initial with
  | nil =>
    cases n <;> rfl
  | cons op rest ih =>
    obtain ⟨k,x⟩ := op
    cases n with
    | zero => exact untouched _ _ _ _ _ (by omega)
    | succ n =>
      have timeEq : t+(n+1) = t+1+n := by omega
      have notPast : t+1 ≤ t+(n+1) := by omega
      by_cases hit : k = a
      · simpa [history,hit,before,replayAt,notPast,timeEq] using ih (t+1) n x
      · simpa [history,hit,replayAt,timeEq] using ih (t+1) n initial

/-- A physical word is observed on its fixed list of bit coordinates. -/
private def weight (word : I → Bool) : List I → Nat
  | [] => 0
  | i :: tail => (if word i then 1 else 0) + weight word tail

private def falls (old new : I → Bool) : List I → Nat
  | [] => 0
  | i :: tail => (if old i && !new i then 1 else 0) + falls old new tail

private def changed (old new : I → Bool) : List I → Nat
  | [] => 0
  | i :: tail => if old i = new i then changed old new tail else 1

private theorem weightCap (word : I → Bool) (indices : List I) :
    weight word indices ≤ indices.length := by
  induction indices with
  | nil => exact Nat.le_refl 0
  | cons i tail ih => cases hi : word i <;> simp [weight,hi] <;> omega

private theorem stepPays (old new : I → Bool) (indices : List I) :
    changed old new indices + weight old indices ≤ 2*falls old new indices + weight new indices := by
  induction indices with
  | nil => exact Nat.le_refl 0
  | cons i tail ih =>
    cases ho : old i <;> cases hn : new i <;>
      simp [changed,weight,falls,ho,hn,Nat.mul_add] <;> omega

def wordChanges (indices : List I) (old : I → Bool) : List (I → Bool) → Nat
  | [] => 0
  | new :: tail => changed old new indices + wordChanges indices new tail

def downFlips (indices : List I) (old : I → Bool) : List (I → Bool) → Nat
  | [] => 0
  | new :: tail => falls old new indices + downFlips indices new tail

private theorem lifetimeCredit (indices : List I) (old : I → Bool) (snapshots : List (I → Bool)) :
    wordChanges indices old snapshots + weight old indices ≤
      2*downFlips indices old snapshots + indices.length := by
  induction snapshots generalizing old with
  | nil => simpa [wordChanges,downFlips] using weightCap old indices
  | cons new rest ih =>
    have first := stepPays old new indices
    have tail := ih new
    simp only [wordChanges,downFlips,Nat.mul_add]
    omega

/-- Simultaneously modifying several bits costs one historical word record
    but may pay several downward flips. Even an arbitrary initial word has
    at most w+2d distinct changes, for d downward flips. -/
theorem wordLifetime (indices : List I) (old : I → Bool) (snapshots : List (I → Bool)) :
    wordChanges indices old snapshots ≤ indices.length + 2*downFlips indices old snapshots := by
  have paid := lifetimeCredit indices old snapshots
  omega

/-- A bounded deterministic computation projected onto probes to the
    still-secret fields. Its terminal payload may include the state, reply,
    work, or every instruction of that branch. -/
inductive ProbeTree (I V S : Type) where
  | done (out : S)
  | ask (field : I) (next : V → ProbeTree I V S)

def outcome (input : I → V) : ProbeTree I V S → S
  | .done out => out
  | .ask i next => outcome input (next (input i))

def probes (input : I → V) : ProbeTree I V S → List I
  | .done _ => []
  | .ask i next => i :: probes input (next (input i))

theorem sameProbePath (tree : ProbeTree I V S) (first later : I → V)
    (agree : ∀ i ∈ probes first tree, later i = first i) :
    outcome later tree = outcome first tree ∧ probes later tree = probes first tree := by
  induction tree with
  | done _ => exact ⟨rfl,rfl⟩
  | ask i next ih =>
    have hv := agree i (.head _)
    have rest := ih (first i) (fun x hx => agree x (.tail i hx))
    simp only [outcome,probes,hv]
    exact ⟨rest.1, congrArg (List.cons i) rest.2⟩

def defaultFill (fixed : I → Option V) (zero : V) (i : I) : V := (fixed i).getD zero

def seals [DecidableEq I] (fixed : I → Option V) (zero : V) (tree : ProbeTree I V S) (i : I) :
    Option V :=
  if i ∈ probes (defaultFill fixed zero) tree then some (defaultFill fixed zero i) else fixed i

def Extends (input : I → V) (fixed : I → Option V) : Prop :=
  ∀ i v, fixed i = some v → input i = v

theorem probeSealsUnsetToZero [DecidableEq I] (fixed : I → Option V) (zero : V)
    (tree : ProbeTree I V S) (i : I) (unbound : fixed i = none)
    (seen : i ∈ probes (defaultFill fixed zero) tree) : seals fixed zero tree i = some zero := by
  simp [seals,seen,defaultFill,unbound]

theorem oldBindingsPersist [DecidableEq I] (fixed : I → Option V) (zero : V)
    (tree : ProbeTree I V S) (i : I) (v : V) (was : fixed i = some v) :
    seals fixed zero tree i = some v := by
  unfold seals
  split <;> simp [defaultFill,was]

/-- Any completed choice of the remaining fields gives exactly the
    terminal result and the same ordered probes as the original zero fill. -/
theorem sealedRunIsGenuine [DecidableEq I] (fixed : I → Option V) (zero : V)
    (tree : ProbeTree I V S) (completion : I → V)
    (agrees : Extends completion (seals fixed zero tree)) :
    outcome completion tree = outcome (defaultFill fixed zero) tree ∧
      probes completion tree = probes (defaultFill fixed zero) tree := by
  apply sameProbePath
  intro i seen
  exact agrees i _ (by simp [seals,seen])

/-- Changing one as-yet-unprobed target preserves the previous computations
    for every legal candidate value of that target. -/
theorem allCurrentTargetsPreserveEarlier [DecidableEq I] (earlier : ProbeTree I V S)
    (input : I → V) (target : I) (untouched : target ∉ probes input earlier) (value : V) :
    let changed := fun i => if i = target then value else input i
    outcome changed earlier = outcome input earlier ∧ probes changed earlier = probes input earlier := by
  apply sameProbePath
  intro i seen
  have ne : i ≠ target := fun eq => untouched (eq ▸ seen)
  simp [ne]

/-- Each finite menu lists all costs of completing the panel, including its
    public dummies, with each possible private target under future-zero fill.
    An already-exposed target can be frozen even if its menu would be cheap. -/
structure LookaheadPanel where
  exposed : Bool
  costs : List Nat
  actualWork : Nat

def worst (p : LookaheadPanel) : Nat := p.costs.foldr max 0
def goodPanel (K : Nat) (p : LookaheadPanel) : Bool := !p.exposed && decide (worst p ≤ K)
def earlyCharge (p : LookaheadPanel) : Nat := if p.exposed then 1 else 0

/-- Taking a most expensive candidate suffices; selecting any slow
    candidate whenever one exists is allowed as well. -/
def ChooseSlow (K : Nat) (p : LookaheadPanel) : Prop :=
  p.exposed = false → (∃ c ∈ p.costs, K < c) → K ≤ p.actualWork

private theorem upperAll (xs : List Nat) (K : Nat) (bounded : ∀ c ∈ xs, c ≤ K) :
    xs.foldr max 0 ≤ K := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons c rest ih =>
    exact Nat.max_le.mpr ⟨bounded c (.head _), ih (fun v hv => bounded v (.tail c hv))⟩

private theorem panelPayment (p : LookaheadPanel) (K : Nat)
    (failed : goodPanel K p = false) (choice : ChooseSlow K p) :
    K ≤ p.actualWork + earlyCharge p*K := by
  cases he : p.exposed with
  | true => simp [earlyCharge,he]
  | false =>
    have expensive : ∃ c ∈ p.costs, K < c := by
      apply Classical.byContradiction
      intro nope
      have bound := upperAll p.costs K (by
        intro c hc
        exact Nat.le_of_not_gt (fun gt => nope ⟨c,hc,gt⟩))
      change worst p ≤ K at bound
      simp [goodPanel,he,bound] at failed
    simpa [earlyCharge,he] using choice he expensive

def rowWork (row : List LookaheadPanel) : Nat := (row.map LookaheadPanel.actualWork).sum
def rowExposures (row : List LookaheadPanel) : Nat := (row.map earlyCharge).sum

private theorem failedRowPayment (row : List LookaheadPanel) (K : Nat)
    (failed : row.any (goodPanel K) = false) (choice : ∀ p ∈ row, ChooseSlow K p) :
    row.length*K ≤ rowWork row + rowExposures row*K := by
  induction row with
  | nil => simp [rowWork,rowExposures]
  | cons p tail ih =>
    have f := Bool.or_eq_false_iff.mp failed
    have a := panelPayment p K f.1 (choice p (.head _))
    have b := ih f.2 (fun x hx => choice x (.tail p hx))
    change (tail.length+1)*K ≤ p.actualWork+rowWork tail + (earlyCharge p + rowExposures tail)*K
    simp only [Nat.add_mul,Nat.one_mul]
    omega

/-- An unsuccessful prefix pays its q panels either in slow work or by the
    distinct private target already exposed *before* that panel. One row is
    one prefix. Each panel has its own word-aligned private target. -/
theorem lookaheadBudget (rows : List (List LookaheadPanel)) (K q : Nat)
    (rule : ∀ row ∈ rows, row.length = q ∧ ∀ p ∈ row, ChooseSlow K p) :
    (rows.filter (fun row => !row.any (goodPanel K))).length*(q*K) ≤
      (rows.map rowWork).sum + (rows.map rowExposures).sum*K := by
  induction rows with
  | nil => simp
  | cons row tail ih =>
    have these := rule row (.head _)
    have later := ih (fun x hx => rule x (.tail row hx))
    cases h : row.any (goodPanel K) with
    | false =>
      have localCost := failedRowPayment row K h these.2
      rw [these.1] at localCost
      simp [h,Nat.add_mul] <;> omega
    | true => simp [h,Nat.add_mul] <;> omega

end PersistedRankQueries
