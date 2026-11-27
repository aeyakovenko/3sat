import Std

/- An adaptive old-word probe simulator for a finite suffix. Known control can
choose any public slot, including the next source or destination of a copy.
No uniform time limit is placed on the free, transcript-dependent computation. -/
namespace SymbolicOldSource

inductive Expr (A W : Type) where
  | known (v : W)
  | unary (a : A) (f : W → W)

def Expr.eval (old : A → W) : Expr A W → W
  | .known v => v
  | .unary a f => f (old a)

def Expr.source : Expr A W → Option A
  | .known _ => none
  | .unary a _ => some a

def Expr.atValue (v : W) : Expr A W → W
  | .known w => w
  | .unary _ f => f v

def Expr.suppress [DecidableEq A] (cells : List A) (values : A → W) : Expr A W → Expr A W
  | .known w => .known w
  | .unary a f => if a ∈ cells then .known (f (values a)) else .unary a f

theorem suppress_sound [DecidableEq A] (old values : A → W) (cells : List A)
    (accurate : ∀ a ∈ cells, values a = old a) (e : Expr A W) :
    (e.suppress cells values).eval old = e.eval old := by
  cases e with
  | known => rfl
  | unary a f =>
    by_cases h : a ∈ cells <;> simp [Expr.suppress, Expr.eval, h, accurate]

theorem suppressed_source_absent [DecidableEq A] (values : A → W) (cells : List A)
    (e : Expr A W) (a : A) (h : a ∈ cells) :
    (e.suppress cells values).source ≠ some a := by
  cases e with
  | known => simp [Expr.suppress, Expr.source]
  | unary b f =>
    by_cases hb : b ∈ cells <;> simp [Expr.suppress, Expr.source, hb]
    rintro rfl
    exact hb h

def sources (xs : List (Expr A W)) : List A := xs.filterMap Expr.source

def merged [Inhabited W] (key : Option A) (op : List W → W) (xs : List (Expr A W)) :
    Expr A W :=
  match key with
  | none => .known (op (xs.map (Expr.atValue default)))
  | some a => .unary a (fun w => op (xs.map (Expr.atValue w)))

theorem merged_sound [Inhabited W] (old : A → W) (key : Option A) (op : List W → W)
    (xs : List (Expr A W)) (same : ∀ a ∈ sources xs, key = some a) :
    (merged key op xs).eval old = op (xs.map (Expr.eval old)) := by
  cases key with
  | none =>
    simp only [merged, Expr.eval]
    apply congrArg op
    apply List.map_congr_left
    intro e he
    cases e with
    | known => rfl
    | unary a f =>
      have h := same a (List.mem_filterMap.mpr ⟨_, he, rfl⟩)
      cases h
  | some a =>
    simp only [merged, Expr.eval]
    apply congrArg op
    apply List.map_congr_left
    intro e he
    cases e with
    | known => rfl
    | unary b f =>
      have eq := Option.some.inj (same b (List.mem_filterMap.mpr ⟨_, he, rfl⟩))
      cases eq
      rfl

def slots (s : S → X) (args : List S) := args.map s
def put [DecidableEq S] (s : S → X) (d : S) (v : X) (i : S) := if i = d then v else s i

/-- After an observed branch the continuation may choose arbitrary new slots,
writes and instructions. Each input program here represents a well-founded
unrolling; a particular bounded clock can also be unrolled to its cutoff. -/
inductive Program (S W : Type) (b : Nat) where
  | halt (out : S)
  | write (dest : S) (args : List S) (bounded : args.length ≤ b)
      (op : List W → W) (next : Program S W b)
  | branch (args : List S) (bounded : args.length ≤ b)
      (next : List W → Program S W b)

def run [DecidableEq S] : Program S W b → (S → W) → W
  | .halt i, s => s i
  | .write d args _ op next, s => run next (put s d (op (slots s args)))
  | .branch args _ next, s => run (next (slots s args)) s

inductive ProbeTree (A W : Type) where
  | halt (answer : W)
  | probe (address : A) (next : W → ProbeTree A W)
  | charge (next : ProbeTree A W)

structure Result (W : Type) where
  answer : W
  probes : Nat
  charged : Nat

def ProbeTree.play (old : A → W) : ProbeTree A W → Result W
  | .halt w => ⟨w, 0, 0⟩
  | .probe a next =>
    let r := (next (old a)).play old
    { r with probes := r.probes + 1 }
  | .charge next =>
    let r := next.play old
    { r with charged := r.charged + 1 }

def gather [DecidableEq A] (cells : List A) (m : A → W)
    (next : (A → W) → ProbeTree A W) : ProbeTree A W :=
  match cells with
  | [] => next m
  | a :: tail => .probe a (fun v => gather tail (put m a v) next)

theorem gather_play [DecidableEq A] (old : A → W) (cells : List A) (m : A → W)
    (next : (A → W) → ProbeTree A W) :
    (gather cells m next).play old =
      let r := (next (fun a => if a ∈ cells then old a else m a)).play old
      { r with probes := r.probes + cells.length } := by
  induction cells generalizing m with
  | nil => simp [gather]
  | cons a tail ih =>
    simp only [gather, ProbeTree.play, ih, List.length_cons]
    have maps : (fun i => if i ∈ tail then old i else put m a (old a) i) =
        (fun i => if i ∈ a :: tail then old i else m i) := by
      funext i
      by_cases h : i ∈ tail <;> by_cases ha : i = a <;> simp [h, ha, put]
    simp [maps, Nat.add_assoc]

/-- Knowing all raw source words for the operand tuple makes the tuple public. -/
theorem observed_slots (s : S → Expr A W) (args : List S) (old values : A → W)
    (accurate : ∀ a ∈ sources (slots s args), values a = old a) :
    slots (fun i => (s i).eval values) args = slots (fun i => (s i).eval old) args := by
  apply List.map_congr_left
  intro i hi
  cases e : s i with
  | known => rfl
  | unary a f =>
    simp [Expr.eval, accurate a (List.mem_filterMap.mpr ⟨_, List.mem_map.mpr ⟨i, hi, e⟩, rfl⟩)]

theorem source_count (s : S → Expr A W) (args : List S) :
    (sources (slots s args)).length ≤ args.length := by
  simpa [sources, slots] using List.length_filterMap_le Expr.source (slots s args)

def chargeIf (flag : Bool) (q : ProbeTree A W) := if flag then .charge q else q

/-- This tree receives public symbolic code and produces actual old-word queries.
It has no argument containing the old words. In a mixed operation we query at
most one address per operand. All occurrences of those labels disappear from
storage, including in slots outside the operand tuple. -/
def simulate [DecidableEq A] [DecidableEq S] [Inhabited W] :
    Program S W b → (S → Expr A W) → ProbeTree A W
  | .halt i, s => match s i with
    | .known v => .halt v
    | .unary a f => .probe a (fun v => .halt (f v))
  | .write d args _ op next, s =>
    let xs := slots s args
    let cells := sources xs
    let key := cells.head?
    if cells.all (fun a => key == some a) then
      simulate next (put s d (merged key op xs))
    else .charge (gather cells (fun _ => default) (fun values =>
      simulate next (put (fun i => (s i).suppress cells values) d
        (.known (op (slots (fun i => (s i).eval values) args))))))
  | .branch args _ next, s =>
    let cells := sources (slots s args)
    chargeIf (!cells.isEmpty) (gather cells (fun _ => default) (fun values =>
      simulate (next (slots (fun i => (s i).eval values) args))
        (fun i => (s i).suppress cells values)))

private theorem eval_put [DecidableEq S] (s : S → Expr A W) (old : A → W)
    (d : S) (e : Expr A W) :
    (fun i => (put s d e i).eval old) = put (fun i => (s i).eval old) d (e.eval old) := by
  funext i
  by_cases h : i = d <;> simp [put, h]

private theorem eval_slots (s : S → Expr A W) (old : A → W) (args : List S) :
    (slots s args).map (Expr.eval old) = slots (fun i => (s i).eval old) args := by
  simp [slots, List.map_map, Function.comp_def]

/-- Simultaneous value and adaptive probe bound, with a charge only for mixing
distinct live source labels or branching on a still-unread label. The '+ 1'
can be attained by a final unchanged payload. -/
theorem simulate_correct [DecidableEq A] [DecidableEq S] [Inhabited W]
    (p : Program S W b) (old : A → W) (s : S → Expr A W) :
    let r := (simulate p s).play old
    r.answer = run p (fun i => (s i).eval old) ∧ r.probes ≤ b * r.charged + 1 := by
  induction p generalizing s with
  | halt i =>
    cases e : s i <;> simp [simulate, e, ProbeTree.play, run, Expr.eval]
  | write d args bound op next ih =>
    let cells := sources (slots s args)
    let key := cells.head?
    change _ ∧ _
    simp only [simulate]
    split
    next shared =>
      have same : ∀ a ∈ cells, key = some a := by
        simpa only [List.all_eq_true, beq_iff_eq] using shared
      obtain ⟨val, cost⟩ := ih (put s d (merged key op (slots s args)))
      exact ⟨by simpa only [eval_put, merged_sound old key op _ same, eval_slots, run] using val, cost⟩
    next mixed =>
      let values := fun a => if a ∈ cells then old a else default
      have accurate : ∀ a ∈ cells, values a = old a := fun a ha => by simp [values, ha]
      have obs := observed_slots s args old values accurate
      have er : (fun i => ((s i).suppress cells values).eval old) =
          (fun i => (s i).eval old) := funext (fun i => suppress_sound old values cells accurate (s i))
      let updated := put (fun i => (s i).suppress cells values) d
        (Expr.known (op (slots (fun i => (s i).eval values) args)))
      obtain ⟨val, cost⟩ := ih updated
      simp only [ProbeTree.play, gather_play]
      change _ = _ ∧ ((simulate next updated).play old).probes + cells.length ≤
        b * (((simulate next updated).play old).charged + 1) + 1
      constructor
      · change ((simulate next updated).play old).answer = _
        rw [val]
        dsimp only [updated]
        rw [eval_put, er]
        change run next (put _ d (op _)) = run next (put _ d (op _))
        rw [obs]
      · have len := Nat.le_trans (source_count s args) bound
        change cells.length ≤ b at len
        rw [Nat.mul_add]
        omega
  | branch args bound next ih =>
    let cells := sources (slots s args)
    let values := fun a => if a ∈ cells then old a else default
    have accurate : ∀ a ∈ cells, values a = old a := fun a ha => by simp [values, ha]
    let nextArgs := slots (fun i => (s i).eval values) args
    let st := fun i => (s i).suppress cells values
    let rest := (simulate (next nextArgs) st).play old
    have obs := observed_slots s args old values accurate
    have er : (fun i => (st i).eval old) = (fun i => (s i).eval old) :=
      funext (fun i => suppress_sound old values cells accurate (s i))
    obtain ⟨val, cost⟩ := ih nextArgs st
    have verdict : rest.answer = run (.branch args bound next) (fun i => (s i).eval old) := by
      change _ = run (next _) _
      rw [val, er]
      rw [show nextArgs = _ from obs]
    change rest.probes ≤ b * rest.charged + 1 at cost
    by_cases empty : cells = []
    · have emp : (sources (slots s args)).isEmpty = true := by change cells.isEmpty = true; simp [empty]
      simp only [simulate, emp, Bool.not_true, chargeIf, Bool.false_eq_true, ↓reduceIte, gather_play]
      change rest.answer = _ ∧ rest.probes + cells.length ≤ b * rest.charged + 1
      simpa only [empty, List.length_nil, Nat.add_zero] using And.intro verdict cost
    · have emp : (sources (slots s args)).isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
      simp only [simulate, emp, Bool.not_false, chargeIf, ↓reduceIte, ProbeTree.play, gather_play]
      change rest.answer = _ ∧ rest.probes + cells.length ≤ b * (rest.charged + 1) + 1
      have len := Nat.le_trans (source_count s args) bound
      change cells.length ≤ b at len
      rw [Nat.mul_add]
      exact ⟨verdict, by omega⟩

/-- Actual probe addresses along one path, including repetitions. -/
def ProbeTree.trace (old : A → W) : ProbeTree A W → List A
  | .halt _ => []
  | .probe a next => a :: (next (old a)).trace old
  | .charge next => next.trace old

theorem trace_length (old : A → W) (t : ProbeTree A W) :
    (t.trace old).length = (t.play old).probes := by
  induction t with
  | halt => rfl
  | probe a next ih => simp [ProbeTree.trace, ProbeTree.play, ih]
  | charge next ih => exact ih

/-- A second memory matching the read cells follows the same adaptive branches,
including their counts of probes and charged operations. -/
theorem replay (old other : A → W) (t : ProbeTree A W)
    (agree : ∀ a ∈ t.trace old, other a = old a) : t.play other = t.play old := by
  induction t with
  | halt => rfl
  | probe a next ih =>
    have value := agree a (by simp [ProbeTree.trace])
    have tail := ih (old a) (fun x hx => agree x (by simp [ProbeTree.trace, hx]))
    simp only [ProbeTree.play, value, tail]
  | charge next ih => simp only [ProbeTree.play, ih agree]

/-- Each particular run gives an old-memory certificate with the very same
public initial symbolic state. Both the addresses and their order can adapt. -/
theorem suffix_certificate [DecidableEq A] [DecidableEq S] [Inhabited W]
    (p : Program S W b) (old : A → W) (s : S → Expr A W) :
    let t := simulate p s
    (t.trace old).length ≤ b * (t.play old).charged + 1 ∧
      ∀ other, (∀ a ∈ t.trace old, other a = old a) →
        run p (fun i => (s i).eval other) = run p (fun i => (s i).eval old) := by
  obtain ⟨verdict, cost⟩ := simulate_correct p old s
  refine ⟨?_, ?_⟩
  · rw [trace_length]
    exact cost
  · intro other agree
    rw [← (simulate_correct p other s).1, replay old other _ agree, verdict]

#print axioms simulate_correct
#print axioms suffix_certificate

end SymbolicOldSource
