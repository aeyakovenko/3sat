import Std

/-! A parsimonious proper 3-CNF extension, from its clauses to its complete model set.
The original variable type counts occurring names, and the private pin vector is arbitrary. -/

namespace ForcedWeightSatModels

/-- A triple forbids one bit pattern on three distinct names. -/
structure Clause (α : Type) where
  i : α
  j : α
  k : α
  bi : Bool
  bj : Bool
  bk : Bool
  proper : i ≠ j ∧ j ≠ k ∧ k ≠ i
  deriving DecidableEq

def Clause.holds (c : Clause α) (x : α → Bool) : Prop :=
  x c.i ≠ c.bi ∨ x c.j ≠ c.bj ∨ x c.k ≠ c.bk

def Models (x : α → Bool) (f : List (Clause α)) : Prop := ∀ c ∈ f, c.holds x

inductive Name (v r : Nat)
  | old (i : Fin v)
  | twin (i : Fin v)
  | a0
  | a1
  | a2
  | pin (j : Fin r)
  deriving DecidableEq

variable {v r : Nat}

def restrict (y : Name v r → Bool) (i : Fin v) := y (.old i)

def liftClause (c : Clause (Fin v)) : Clause (Name v r) :=
  ⟨.old c.i, .old c.j, .old c.k, c.bi, c.bj, c.bk, by simpa using c.proper⟩

def anchor (a b c : Bool) : Clause (Name v r) := ⟨.a0, .a1, .a2, a, b, c, by simp⟩

def anchorRows : List (Clause (Name v r)) :=
  [anchor false false true, anchor false true false, anchor false true true,
   anchor true false false, anchor true false true, anchor true true false, anchor true true true]

theorem seven_distinct : (@anchorRows v r).length = 7 ∧ (@anchorRows v r).Nodup := by
  simp [anchorRows, anchor]

def twinRows (i : Fin v) : List (Clause (Name v r)) :=
  [⟨.old i, .twin i, .a0, false, false, false, by simp⟩,
   ⟨.old i, .twin i, .a0, true, true, false, by simp⟩]

def pinRow (target : Fin r → Bool) (j : Fin r) : Clause (Name v r) :=
  ⟨.pin j, .a0, .a1, !(target j), false, false, by simp⟩

def extendFormula (f : List (Clause (Fin v))) (target : Fin r → Bool) : List (Clause (Name v r)) :=
  f.map liftClause ++ anchorRows ++ (List.finRange v).flatMap twinRows ++
    (List.finRange r).map (pinRow target)

theorem extended_clause_count (f : List (Clause (Fin v))) (target : Fin r → Bool) :
    (extendFormula f target).length = f.length + 7 + v * 2 + r := by
  simp [extendFormula, List.length_flatMap, twinRows, anchorRows, List.map_const', List.sum_replicate_nat]
  omega

def extend (x : Fin v → Bool) (target : Fin r → Bool) : Name v r → Bool
  | .old i => x i
  | .twin i => !(x i)
  | .a0 | .a1 | .a2 => false
  | .pin j => target j

private theorem fin_mem (j : Fin r) : j ∈ List.finRange r := by
  have h := List.getElem_mem (l := List.finRange r) (n := j.val) (by simp)
  simpa using h

private theorem models_append (x : α → Bool) (a b : List (Clause α)) :
    Models x (a ++ b) ↔ Models x a ∧ Models x b := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨ha, hb⟩ c hc
    exact (List.mem_append.mp hc).elim (ha c) (hb c)

private theorem models_lift (y : Name v r → Bool) (f : List (Clause (Fin v))) :
    Models y (f.map liftClause) ↔ Models (restrict y) f := by
  simp [Models, Clause.holds, liftClause, restrict]

private theorem models_anchors (y : Name v r → Bool) :
    Models y anchorRows ↔ y .a0 = false ∧ y .a1 = false ∧ y .a2 = false := by
  cases h0 : y .a0 <;> cases h1 : y .a1 <;> cases h2 : y .a2 <;>
    simp [Models, anchorRows, Clause.holds, anchor, h0, h1, h2]

private theorem models_twins (y : Name v r → Bool) (h0 : y .a0 = false) :
    Models y ((List.finRange v).flatMap twinRows) ↔ ∀ i, y (.twin i) = !(y (.old i)) := by
  have one (i : Fin v) : Models y (twinRows i) ↔ y (.twin i) = !(y (.old i)) := by
    cases hx : y (.old i) <;> cases hy : y (.twin i) <;>
      simp [Models, twinRows, Clause.holds, h0, hx, hy]
  constructor
  · intro h i
    apply (one i).1
    intro c hc
    exact h c (List.mem_flatMap.mpr ⟨i, fin_mem i, hc⟩)
  · intro h c hc
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hc
    exact (one i).2 (h i) c hi

private theorem models_pins (y : Name v r → Bool) (target : Fin r → Bool)
    (h0 : y .a0 = false) (h1 : y .a1 = false) :
    Models y ((List.finRange r).map (pinRow target)) ↔ ∀ j, y (.pin j) = target j := by
  have one (j : Fin r) : (pinRow target j).holds y ↔ y (.pin j) = target j := by
    cases hp : y (.pin j) <;> cases ht : target j <;> simp [Clause.holds, pinRow, h0, h1, hp, ht]
  constructor
  · intro h j
    exact (one j).1 (h _ (List.mem_map.mpr ⟨j, fin_mem j, rfl⟩))
  · intro h c hc
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
    exact (one j).2 (h j)

/-- Every extended model is exactly the canonical extension of its projected old model. -/
theorem models_iff (y : Name v r → Bool) (f : List (Clause (Fin v))) (target : Fin r → Bool) :
    Models y (extendFormula f target) ↔ Models (restrict y) f ∧ y = extend (restrict y) target := by
  simp only [extendFormula, models_append, models_lift, models_anchors]
  constructor
  · rintro ⟨⟨⟨old, h0, h1, h2⟩, twins⟩, pins⟩
    refine ⟨old, ?_⟩
    funext n
    cases n with
    | old i => rfl
    | twin i => exact (models_twins y h0).1 twins i
    | a0 => exact h0
    | a1 => exact h1
    | a2 => exact h2
    | pin j => exact (models_pins y target h0 h1).1 pins j
  · rintro ⟨old, canonical⟩
    have atName (n : Name v r) := congrFun canonical n
    have h0 : y .a0 = false := atName .a0
    have h1 : y .a1 = false := atName .a1
    have h2 : y .a2 = false := atName .a2
    exact ⟨⟨⟨old, h0, h1, h2⟩, (models_twins y h0).2 (fun i => atName (.twin i))⟩,
      (models_pins y target h0 h1).2 (fun j => atName (.pin j))⟩

/-- A specified old model has a unique extension agreeing on all old variables. -/
theorem unique_extension {x : Fin v → Bool} {f : List (Clause (Fin v))}
    (old : Models x f) (target : Fin r → Bool) :
    ∃ y, (Models y (extendFormula f target) ∧ restrict y = x) ∧
      ∀ z, Models z (extendFormula f target) → restrict z = x → z = y := by
  refine ⟨extend x target, ⟨(models_iff _ _ _).2 ⟨old, rfl⟩, rfl⟩, ?_⟩
  intro z hz hx
  rw [((models_iff _ _ _).1 hz).2, hx]

theorem equisatisfiable (f : List (Clause (Fin v))) (target : Fin r → Bool) :
    (∃ y, Models y (extendFormula f target)) ↔ ∃ x, Models x f := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨restrict y, ((models_iff _ _ _).1 hy).1⟩
  · rintro ⟨x, hx⟩
    exact ⟨extend x target, (models_iff _ _ _).2 ⟨hx, rfl⟩⟩

def count (xs : List α) (f : α → Bool) := xs.countP f

private theorem count_twins (xs : List α) (f : α → Bool) :
    count xs f + count xs (fun i => !(f i)) = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : f a <;> simp [count, List.countP_cons, h] at * <;> omega

/-- Explicit census includes all three anchors and every private pin. -/
def weight (y : Name v r → Bool) : Nat :=
  count (List.finRange v) (fun i => y (.old i)) +
  count (List.finRange v) (fun i => y (.twin i)) +
  count [Name.a0, .a1, .a2] y + count (List.finRange r) (fun j => y (.pin j))

theorem model_weight {f : List (Clause (Fin v))} {target : Fin r → Bool} {y : Name v r → Bool}
    (h : Models y (extendFormula f target)) :
    weight y = v + count (List.finRange r) target := by
  obtain ⟨_, eqn⟩ := (models_iff _ _ _).1 h
  rw [eqn]
  simp only [weight, extend, count_twins, List.length_finRange]
  rfl

end ForcedWeightSatModels
