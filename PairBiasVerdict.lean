import Std

namespace PairBiasVerdict

/-- Each link is a conjunction of the actual ternary clauses. -/
def freeLink (lit a b : Bool) : Prop :=
  ((lit || !a || b) && (lit || a || !b)) = true

def xorLink (x a b : Bool) : Prop :=
  ((x || a || !b) && (x || !a || b) &&
   (!x || a || b) && (!x || !a || !b)) = true

theorem freeLink_iff (x a b : Bool) : freeLink x a b ↔ x = true ∨ a = b := by
  unfold freeLink
  cases x <;> cases a <;> cases b <;> decide

theorem xorLink_iff (x a b : Bool) : xorLink x a b ↔ b = (a ^^ x) := by
  unfold xorLink
  cases x <;> cases a <;> cases b <;> decide

/-- The intermediate states are fresh existentially quantified Boolean variables. -/
def path (link : Bool → Bool → Bool → Prop) (a b : Bool) : List Bool → Prop
  | [] => a = b
  | x :: xs => ∃ next, link x a next ∧ path link next b xs

def cycle (link : Bool → Bool → Bool → Prop) (xs : List Bool) : Prop :=
  ∃ seed, path link seed (!seed) xs

private theorem free_path (xs : List Bool) (a b : Bool) :
    path freeLink a b xs ↔ a = b ∨ true ∈ xs := by
  induction xs generalizing a b with
  | nil => simp [path]
  | cons x xs ih =>
    simp only [path, freeLink_iff, ih, List.mem_cons]
    cases x <;> cases a <;> cases b <;> simp

theorem free_cycle (xs : List Bool) : cycle freeLink xs ↔ true ∈ xs := by
  constructor
  · rintro ⟨a, h⟩
    rcases (free_path xs a (!a)).mp h with heq | hi
    · cases a <;> contradiction
    · exact hi
  · intro h
    exact ⟨false, (free_path xs false true).mpr (Or.inr h)⟩

def parity : List Bool → Bool
  | [] => false
  | x :: xs => x ^^ parity xs

private theorem xor_path (xs : List Bool) (a b : Bool) :
    path xorLink a b xs ↔ b = (a ^^ parity xs) := by
  induction xs generalizing a with
  | nil => simp [path, parity, eq_comm]
  | cons x xs ih =>
    simp [path, xorLink_iff, ih, parity, Bool.xor_assoc]

theorem xor_cycle (xs : List Bool) : cycle xorLink xs ↔ parity xs = true := by
  unfold cycle
  simp only [xor_path]
  cases parity xs <;> decide

abbrev Shares := Fin 3 → Bool

def decode (x : Shares) : Bool := x 0 ^^ x 1 ^^ x 2

def encode (b : Bool) : Shares := fun i => if i = 0 then b else false

@[simp] theorem decode_encode (b : Bool) : decode (encode b) = b := by
  simp [decode, encode]

/-- Raw coordinates occur by share layer, in the order used by the compiler. -/
def differences {q : Nat} (x p : Fin q → Shares) : List Bool :=
  (List.ofFn (fun j : Fin 3 => List.ofFn (fun i : Fin q => x i j != p i j))).flatten

theorem differences_hit {q : Nat} (x p : Fin q → Shares) :
    true ∈ differences x p ↔ x ≠ p := by
  simp only [differences, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨layer, ⟨j, rfl⟩, hit⟩ rfl
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hit
    simp at hi
  · intro h
    have pair : ∃ j i, x i j ≠ p i j := by
      apply Classical.byContradiction
      intro n
      apply h
      funext i j
      exact Classical.byContradiction (fun ne => n ⟨j, i, ne⟩)
    obtain ⟨j, i, ne⟩ := pair
    refine ⟨_, ⟨j, rfl⟩, List.mem_ofFn.mpr ⟨i, ?_⟩⟩
    simpa using ne

/-- There is a separate cycle of fresh states for every forbidden raw pattern. -/
def excludeFiber {q : Nat} (x : Fin q → Shares) (bad : Fin q → Bool) : Prop :=
  ∀ p : Fin q → Shares, (fun i => decode (p i)) = bad → cycle freeLink (differences x p)

theorem excludeFiber_iff {q : Nat} (x : Fin q → Shares) (bad : Fin q → Bool) :
    excludeFiber x bad ↔ (fun i => decode (x i)) ≠ bad := by
  constructor
  · intro h hit
    exact (differences_hit x x).mp ((free_cycle _).mp (h x hit)) rfl
  · intro ne p hp
    apply (free_cycle _).mpr
    apply (differences_hit x p).mpr
    rintro rfl
    exact ne hp

structure Clause (V : Type) where
  var : Fin 3 → V
  /-- The unique vector of values on these ordered ports that falsifies the clause. -/
  bad : Fin 3 → Bool

structure Block (V : Type) where
  act : Shares
  data : V → Shares

def prepend {A : Type} {q : Nat} (a : A) (rest : Fin q → A) : Fin (q+1) → A :=
  Fin.cases a rest

private theorem prepend_eq {A : Type} {q : Nat} (a b : A) (u v : Fin q → A) :
    prepend a u = prepend b v ↔ a = b ∧ u = v := by
  constructor
  · intro h
    exact ⟨congrFun h 0, funext (fun i => congrFun h i.succ)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem decode_prepend {q : Nat} (a : Shares) (r : Fin q → Shares) :
    (fun i => decode (prepend a r i)) = prepend (decode a) (fun i => decode (r i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def sourceClause {V : Type} (x : V → Bool) (c : Clause V) : Prop :=
  (fun i => x (c.var i)) ≠ c.bad

def physicalClause {V : Type} (b : Block V) (c : Clause V) : Prop :=
  let sides := fun i => b.data (c.var i)
  if decode c.bad then excludeFiber sides c.bad
  else excludeFiber (prepend b.act sides) (prepend true c.bad)

theorem physicalClause_iff {V : Type} (b : Block V) (c : Clause V) :
    physicalClause b c ↔ sourceClause (fun v => decode (b.data v)) c ∨
      (decode c.bad = false ∧ decode b.act = false) := by
  cases h : decode c.bad <;> simp only [physicalClause, h, Bool.false_eq_true,
    Bool.true_eq_false, if_true, if_false, excludeFiber_iff, decode_prepend,
    prepend_eq, sourceClause, true_and, false_and, or_false]
  cases decode b.act <;> simp [prepend_eq]

def ofLogical {V : Type} (a : Bool) (x : V → Bool) : Block V :=
  ⟨encode a, fun v => encode (x v)⟩

private theorem idle_clause {V : Type} (c : Clause V) :
    physicalClause (ofLogical false (fun _ => false)) c := by
  apply (physicalClause_iff _ _).mpr
  by_cases h : decode c.bad = false
  · exact Or.inr ⟨h, by simp [ofLogical]⟩
  · apply Or.inl
    intro allZero
    apply h
    have e : (fun _ : Fin 3 => false) = c.bad := by
      simpa [ofLogical] using allZero
    rw [← e]
    rfl

private theorem parity_append (xs ys : List Bool) :
    parity (xs ++ ys) = (parity xs ^^ parity ys) := by
  induction xs with
  | nil => simp [parity]
  | cons a xs ih => simp [parity, ih, Bool.xor_assoc]

/-- The global XOR uses the same interleaved physical order as the ternary tests. -/
def activationLinks {V : Type} (bs : List (Block V)) : List Bool :=
  bs.map (fun b => b.act 0) ++ bs.map (fun b => b.act 1) ++ bs.map (fun b => b.act 2)

theorem activation_parity {V : Type} (bs : List (Block V)) :
    parity (activationLinks bs) = parity (bs.map (fun b => decode b.act)) := by
  simp only [activationLinks, parity_append]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, parity]
    rw [← ih]
    simp only [decode, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

private theorem has_active {V : Type} (bs : List (Block V))
    (h : parity (bs.map (fun b => decode b.act)) = true) :
    ∃ b ∈ bs, decode b.act = true := by
  induction bs with
  | nil => contradiction
  | cons b bs ih =>
    cases hb : decode b.act with
    | false =>
      obtain ⟨b', mem, act⟩ := ih (by simpa [parity, hb] using h)
      exact ⟨b', List.mem_cons_of_mem _ mem, act⟩
    | true => exact ⟨b, by simp, hb⟩

private theorem rep_idle_parity {V : Type} (n : Nat) :
    parity ((List.replicate n (ofLogical false (fun _ : V => false))).map
      (fun b => decode b.act)) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, parity, ofLogical] using ih

/-- Distinct tests have private states. Raw variables are shared within each
    block, and its activation shares are also read by the common parity cycle. -/
def compiledSat {V : Type} (f : List (Clause V)) (t : Nat) : Prop :=
  ∃ bs : List (Block V), bs.length = t ∧ cycle xorLink (activationLinks bs) ∧
    ∀ b ∈ bs, ∀ c ∈ f, physicalClause b c

/-- The compiled formula with n+1 blocks has a satisfying physical assignment
    exactly when the original formula has a satisfying assignment. -/
theorem compiled_verdict {V : Type} (f : List (Clause V)) (n : Nat) :
    compiledSat f (n+1) ↔ ∃ x : V → Bool, ∀ c ∈ f, sourceClause x c := by
  constructor
  · rintro ⟨bs, _, global, rows⟩
    obtain ⟨b, mem, act⟩ := has_active bs (by
      rw [← activation_parity]
      exact (xor_cycle _).mp global)
    refine ⟨fun v => decode (b.data v), fun c hc => ?_⟩
    rcases (physicalClause_iff _ _).mp (rows b mem c hc) with sat | idle
    · exact sat
    · simp [act] at idle
  · rintro ⟨x, works⟩
    let active := ofLogical true x
    let idle := ofLogical false (fun _ : V => false)
    refine ⟨active :: List.replicate n idle, by simp, (xor_cycle _).mpr ?_, ?_⟩
    · rw [activation_parity]
      simp only [List.map_cons, parity, active, idle, ofLogical, decode_encode]
      simpa [ofLogical] using rep_idle_parity (V := V) n
    · intro b hb c hc
      rcases List.mem_cons.mp hb with rfl | rest
      · apply (physicalClause_iff _ _).mpr
        left
        simpa [active, ofLogical] using works c hc
      · obtain rfl := (List.mem_replicate.mp rest).2
        exact idle_clause c


/-- A concrete assignment stores the initial bit and one state at each interior
    position. The final, complemented bit is read from the initial state. -/
structure Tape where
  seed : Bool
  interior : List Bool
deriving Inhabited

def checks (link : Bool → Bool → Bool → Prop) (a b : Bool) :
    List Bool → List Bool → Prop
  | [], [] => a = b
  | [x], [] => link x a b
  | x :: y :: ys, z :: zs => link x a z ∧ checks link z b (y :: ys) zs
  | _, _ => False

def onTape (link : Bool → Bool → Bool → Prop) (xs : List Bool) (s : Tape) : Prop :=
  checks link s.seed (!s.seed) xs s.interior

private theorem tape_path (link : Bool → Bool → Bool → Prop) (xs : List Bool) (a b : Bool) :
    (∃ states, checks link a b xs states) ↔ path link a b xs := by
  induction xs generalizing a with
  | nil =>
    constructor
    · rintro ⟨s, h⟩
      cases s <;> simp_all [checks, path]
    · intro h
      exact ⟨[], h⟩
  | cons x tail ih =>
    cases tail with
    | nil =>
      constructor
      · rintro ⟨s, h⟩
        cases s with
        | nil => exact ⟨b, h, rfl⟩
        | cons _ _ => contradiction
      · rintro ⟨z, edge, rfl⟩
        exact ⟨[], edge⟩
    | cons y tail =>
      constructor
      · rintro ⟨s, h⟩
        cases s with
        | nil => contradiction
        | cons z zs => exact ⟨z, h.1, (ih z).mp ⟨zs, h.2⟩⟩
      · rintro ⟨z, edge, rest⟩
        obtain ⟨zs, good⟩ := (ih z).mpr rest
        exact ⟨z :: zs, edge, good⟩

private theorem tape_cycle (link : Bool → Bool → Bool → Prop) (xs : List Bool) :
    (∃ s, onTape link xs s) ↔ cycle link xs := by
  constructor
  · rintro ⟨s, h⟩
    exact ⟨s.seed, (tape_path _ _ _ _).mp ⟨s.interior, h⟩⟩
  · rintro ⟨seed, h⟩
    obtain ⟨zs, good⟩ := (tape_path _ _ _ _).mpr h
    exact ⟨⟨seed, zs⟩, good⟩

def assignedFiber {q : Nat} (x : Fin q → Shares) (bad : Fin q → Bool)
    (table : (Fin q → Shares) → Tape) : Prop :=
  ∀ p, (fun i => decode (p i)) = bad → onTape freeLink (differences x p) (table p)

private theorem fiber_tables {q : Nat} (x : Fin q → Shares) (bad : Fin q → Bool) :
    (∃ table, assignedFiber x bad table) ↔ excludeFiber x bad := by
  constructor
  · rintro ⟨table, ok⟩ p hp
    exact (tape_cycle _ _).mp ⟨table p, ok p hp⟩
  · intro h
    have allPatterns (p : Fin q → Shares) :
        ∃ tape, (fun i => decode (p i)) = bad → onTape freeLink (differences x p) tape := by
      by_cases hp : (fun i => decode (p i)) = bad
      · obtain ⟨tape, ht⟩ := (tape_cycle _ _).mpr (h p hp)
        exact ⟨tape, fun _ => ht⟩
      · exact ⟨default, fun eq => (hp eq).elim⟩
    exact ⟨fun p => (allPatterns p).choose, fun p => (allPatterns p).choose_spec⟩

structure RowTapes where
  unguarded : (Fin 3 → Shares) → Tape
  guarded : (Fin 4 → Shares) → Tape

def assignedClause {V : Type} (b : Block V) (c : Clause V) (s : RowTapes) : Prop :=
  let sides := fun i => b.data (c.var i)
  if decode c.bad then assignedFiber sides c.bad s.unguarded
  else assignedFiber (prepend b.act sides) (prepend true c.bad) s.guarded

private theorem row_tables {V : Type} (b : Block V) (c : Clause V) :
    (∃ s, assignedClause b c s) ↔ physicalClause b c := by
  cases h : decode c.bad <;> simp only [assignedClause, physicalClause, h,
    Bool.false_eq_true, if_true, if_false, ← fiber_tables]
  · constructor
    · rintro ⟨s, ok⟩
      exact ⟨s.guarded, ok⟩
    · rintro ⟨t, ok⟩
      exact ⟨⟨fun _ => default, t⟩, ok⟩
  · constructor
    · rintro ⟨s, ok⟩
      exact ⟨s.unguarded, ok⟩
    · rintro ⟨t, ok⟩
      exact ⟨⟨t, fun _ => default⟩, ok⟩

/-- A single physical assignment fixes all raw bits, all global cycle states,
    and the distinct state arrays for every block, clause occurrence and forbidden
    raw pattern, before checking any of their ternary constraints. -/
def physicalSat {V : Type} (f : List (Clause V)) (t : Nat) : Prop :=
  ∃ bs : List (Block V), bs.length = t ∧
    ∃ (global : Tape) (rows : Fin bs.length → Fin f.length → RowTapes),
      onTape xorLink (activationLinks bs) global ∧
      ∀ i j, assignedClause (bs.get i) (f.get j) (rows i j)

theorem physical_verdict {V : Type} (f : List (Clause V)) (n : Nat) :
    physicalSat f (n+1) ↔ ∃ x : V → Bool, ∀ c ∈ f, sourceClause x c := by
  rw [← compiled_verdict]
  constructor
  · rintro ⟨bs, len, g, rows, hg, hr⟩
    refine ⟨bs, len, (tape_cycle _ _).mp ⟨g, hg⟩, ?_⟩
    intro b hb c hc
    obtain ⟨i, rfl⟩ := List.get_of_mem hb
    obtain ⟨j, rfl⟩ := List.get_of_mem hc
    exact (row_tables _ _).mp ⟨rows i j, hr i j⟩
  · rintro ⟨bs, len, hg, hr⟩
    obtain ⟨g, ok⟩ := (tape_cycle _ _).mpr hg
    have each (i : Fin bs.length) (j : Fin f.length) :=
      (row_tables (bs.get i) (f.get j)).mpr (hr _ (bs.get_mem i) _ (f.get_mem j))
    exact ⟨bs, len, g, fun i j => (each i j).choose, ok, fun i j => (each i j).choose_spec⟩

end PairBiasVerdict
