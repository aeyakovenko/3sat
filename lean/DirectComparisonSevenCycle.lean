import Std

namespace DirectComparisonSevenCycle

/-- Bit r of a row set denotes the input mask r, 0 ≤ r < 128. -/
def rowSet (f : Nat → Bool) : Nat :=
  (List.range 128).foldl (fun acc r => if f r then acc ||| (1 <<< r) else acc) 0

def full : Nat := 2^128 - 1

def yesRows : Nat := rowSet (fun r =>
  (List.range 7).all fun i => r.testBit i || r.testBit ((i+1)%7))

def noRows : Nat := full ^^^ yesRows

/-- Codes 0, 1, 2 denote a loaded three-bit input word. Codes 3 through 10
denote the eight immediate words. Every remaining direct address holds zero. -/
def argValue (r a : Nat) : Nat :=
  if a < 3 then (r >>> (3 * a)) % 8 else a - 3

inductive Cmp | eq | ult | slt

def compareWords : Cmp → Nat → Nat → Bool
  | .eq, x, y => x == y
  | .ult, x, y => x < y
  | .slt, x, y => (x ^^^ 4) < (y ^^^ 4)

def available (loaded : Nat) : List Nat :=
  (List.range 11).filter (fun a => decide (3 ≤ a) || loaded.testBit a)

def guardMask (op : Cmp) (a b : Nat) : Nat :=
  rowSet fun r => compareWords op (argValue r a) (argValue r b)

def guardList (loaded : Nat) : List Nat :=
  (([Cmp.eq, .ult, .slt].flatMap fun op =>
    (available loaded).flatMap fun a =>
      (available loaded).map fun b => guardMask op a b)).eraseDups

def guardTable : Array (List Nat) :=
  ((List.range 8).map guardList).toArray

def guards (loaded : Nat) : List Nat := guardTable[loaded]?.getD []

def destinations : List Nat := [0,1,2]
def mixedFree (r : Nat) : Bool := (r &&& noRows == 0) || (r &&& yesRows == 0)
def second (r q : Nat) : Nat := r &&& (full ^^^ q)

/-- A normalized program unrolling: unlimited registers retain all direct words
already loaded, and immediate comparisons are free to mention any word constant.
Both children of each comparison have one less tick. Repeated loads and constant
comparisons are allowed, including actions that give no new information.
The budget is a worst-case bound. -/
inductive Fits : Nat → Nat → Nat → Prop where
  | halt {d a r} (h : mixedFree r = true) : Fits d a r
  | load {d a r i} (hi : i ∈ destinations)
      (next : Fits d (a ||| (1 <<< i)) r) : Fits (d+1) a r
  | branch {d a r q} (hq : q ∈ guards a)
      (yes : Fits d a (r &&& q)) (no : Fits d a (second r q)) : Fits (d+1) a r

def possible : Nat → Nat → Nat → Bool
  | 0, _, r => mixedFree r
  | d+1, a, r => mixedFree r ||
      destinations.any (fun i => possible d (a ||| (1 <<< i)) r) ||
      (guards a).any fun q => possible d a (r &&& q) && possible d a (second r q)

theorem fits_iff (d a r : Nat) : Fits d a r ↔ possible d a r = true := by
  induction d generalizing a r with
  | zero =>
    constructor
    · intro h
      cases h with | halt h => exact h
    · exact Fits.halt
  | succ d ih =>
    simp only [possible, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      ← ih]
    constructor
    · intro h
      cases h with
      | halt h => exact Or.inl (Or.inl h)
      | load hi next => exact Or.inl (Or.inr ⟨_, hi, next⟩)
      | branch hq yes no => exact Or.inr ⟨_, hq, yes, no⟩
    · rintro ((h|⟨i,hi,k⟩)|⟨q,hq,l,t⟩)
      · exact .halt h
      · exact .load hi k
      · exact .branch hq l t

/-- Nat hashing uses the low 64 bits. Include the upper half of the 128-row
set in the cache key so that rows 64 through 127 also affect its hash. -/
abbrev Key := Nat × Nat × Nat × Nat
abbrev Cert (b : Bool) := {value : Bool // value = b}
abbrev Cache := Std.DHashMap Key (fun k => Cert (possible k.1 k.2.1 k.2.2.2))

/-- The type of each cache entry certifies equality to the structural recursion. -/
def anyCached {α} {p : α → Bool} (f : (x : α) → StateM Cache (Cert (p x))) :
    (xs : List α) → StateM Cache (Cert (xs.any p))
  | [] => pure ⟨false, rfl⟩
  | x :: xs => do
    let ⟨v, h⟩ ← f x
    if hv : v then
      return ⟨true, by simp [List.any_cons, ← h, hv]⟩
    else
      let ⟨w, hw⟩ ← anyCached f xs
      return ⟨w, by simp [List.any_cons, ← h, hv, hw]⟩

def cached : (d a r : Nat) → StateM Cache (Cert (possible d a r))
  | 0, _, r => pure ⟨mixedFree r, rfl⟩
  | d+1, a, r => do
    let k : Key := (d+1, a, r >>> 64, r)
    if let some w := (← get).get? k then return w
    let ans ← calcHere d a r
    modify (fun m => m.insert k ans)
    return ans
where
  calcHere (d a r : Nat) : StateM Cache (Cert (possible (d+1) a r)) := do
    if hm : mixedFree r then return ⟨true, by simp [possible, hm]⟩
    else
      let ⟨u, hu⟩ ← anyCached (p := fun i => possible d (a ||| (1 <<< i)) r)
        (fun i => cached d (a ||| (1 <<< i)) r) destinations
      if h : u then return ⟨true, by simp [possible, ← hu, h]⟩
      else
        let ⟨v, hv⟩ ← anyCached (p := fun q =>
          possible d a (r &&& q) && possible d a (second r q)) (fun q => do
            let ⟨left, hl⟩ ← cached d a (r &&& q)
            if hleft : left then
              let ⟨right, hr⟩ ← cached d a (second r q)
              return ⟨right, by simp [← hl, hleft, hr]⟩
            else
              return ⟨false, by simp [← hl, hleft]⟩) (guards a)
        return ⟨v, by simp [possible, hm, ← hu, h, hv]⟩

def answer (d : Nat) : Cert (possible d 0 full) := (cached d 0 full).run' {}

theorem seven_is_impossible : ¬ Fits 7 0 full := by
  rw [fits_iff, ← (answer 7).property]
  native_decide

/-- Every available native comparison occurs in the DP guard enumeration. -/
theorem guard_member (a : Fin 8) (op : Cmp) {x y : Fin 11}
    (hx : x.val ∈ available a) (hy : y.val ∈ available a) :
    guardMask op x y ∈ guards a := by
  revert a x y
  cases op <;> native_decide

def withWord (a : Fin 8) (i : Fin 3) : Fin 8 :=
  ⟨a.val ||| (1 <<< i.val), (by
    have h : ∀ (v : Fin 8) (j : Fin 3), v.val ||| (1 <<< j.val) < 8 := by native_decide
    exact h a i)⟩

/-- Syntax of finite-budget direct programs. Retaining all loaded words for
future reads models an unlimited supply of registers. The destination of each
load and both comparison operands may vary freely from node to node. -/
inductive Tree : Fin 8 → Nat → Type where
  | halt {a d} (v : Bool) : Tree a d
  | load {a d} (i : Fin 3) (child : Tree (withWord a i) d) : Tree a (d+1)
  | branch {a : Fin 8} {d : Nat} (op : Cmp) (x y : Fin 11)
      (hx : x.val ∈ available a) (hy : y.val ∈ available a)
      (left right : Tree a d) : Tree a (d+1)

def eval {a d} : Tree a d → Fin 128 → Bool
  | .halt v, _ => v
  | .load _ child, i => eval child i
  | .branch op x y _ _ left right, i =>
    if compareWords op (argValue i x) (argValue i y) then eval left i else eval right i

def Supported (r : Nat) : Prop := ∀ i, 128 ≤ i → r.testBit i = false

private theorem supported_and {r : Nat} (h : Supported r) (q : Nat) :
    Supported (r &&& q) := by
  intro i hi
  simp [h i hi]

private theorem guard_bit (op : Cmp) (x y : Fin 11) (i : Fin 128) :
    (guardMask op x y).testBit i = compareWords op (argValue i x) (argValue i y) := by
  revert x y i
  cases op <;> native_decide

private theorem full_bit (i : Fin 128) : full.testBit i = true := by
  unfold full
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true i.isLt

private theorem disjoint {r q : Nat} (s : Supported r)
    (h : ∀ i : Fin 128, r.testBit i = true → q.testBit i = false) : r &&& q = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hlt : j < 128
  · cases hj : r.testBit j with
    | false => simp [hj]
    | true => simp [hj, h ⟨j,hlt⟩ hj]
  · simp [s j (by omega)]

private theorem tree_fits {a d} (t : Tree a d) (r : Nat) (sr : Supported r)
    (correct : ∀ i : Fin 128, r.testBit i = true → eval t i = yesRows.testBit i) :
    Fits d a r := by
  induction t generalizing r with
  | halt v =>
    apply Fits.halt
    cases v with
    | false =>
      have h := disjoint sr (q := yesRows) (fun i hi => (correct i hi).symm)
      simp [mixedFree, h]
    | true =>
      have h := disjoint sr (q := noRows) (fun i hi => by
        have hy : yesRows.testBit i = true := (correct i hi).symm
        simp [noRows, full_bit, hy])
      simp [mixedFree, h]
  | load i child ih =>
    exact Fits.load (i := i.val) (by have hi := i.isLt; simp [destinations]; omega)
      (ih r sr correct)
  | @branch a d op x y hx hy left right ihL ihR =>
    apply Fits.branch (guard_member a op hx hy)
    · apply ihL _ (supported_and sr _)
      intro i hi
      simp only [Nat.testBit_and, Bool.and_eq_true, guard_bit] at hi
      simpa [eval, hi.2] using correct i hi.1
    · apply ihR _ (supported_and sr _)
      intro i hi
      simp only [second, Nat.testBit_and, Bool.and_eq_true, Nat.testBit_xor,
        full_bit, guard_bit, Bool.true_xor, Bool.not_eq_true'] at hi
      simpa [eval, hi.2] using correct i hi.1

def isCover (r : Nat) : Bool :=
  (List.range 7).all fun i => r.testBit i || r.testBit ((i+1)%7)

theorem no_seven_step_direct_program (t : Tree 0 7) :
    ¬ ∀ i : Fin 128, eval t i = isCover i := by
  intro h
  have hf : Supported full := by
    intro i hi
    unfold full
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_false (Nat.not_lt.mpr hi)
  have hy : ∀ i : Fin 128, yesRows.testBit i = isCover i := by native_decide
  apply seven_is_impossible
  exact tree_fits t full hf (fun i _ => (h i).trans (hy i).symm)

/-- Direct eight-step witness; the typechecks of both membership arguments at
each comparison guarantee its operands have been loaded or are immediate. -/
def eightProgram : Tree 0 8 :=
  .load 0 (.branch .eq 0 5 (by decide) (by decide)
      (.load 1 (.branch .eq 0 1 (by decide) (by decide)
          (.halt false)
          (.branch .ult 1 8 (by decide) (by decide)
            (.branch .eq 1 6 (by decide) (by decide)
              (.load 2 (.branch .eq 2 3 (by decide) (by decide)
                  (.halt false)
                  (.halt true)))
              (.halt false))
            (.branch .eq 1 9 (by decide) (by decide)
              (.halt false)
              (.load 2 (.branch .eq 2 3 (by decide) (by decide)
                  (.halt false)
                  (.halt true)))))))
      (.branch .ult 0 8 (by decide) (by decide)
        (.branch .eq 0 6 (by decide) (by decide)
          (.load 1 (.branch .eq 0 1 (by decide) (by decide)
              (.load 2 (.branch .eq 2 3 (by decide) (by decide)
                  (.halt false)
                  (.halt true)))
              (.branch .eq 1 8 (by decide) (by decide)
                (.halt true)
                (.branch .eq 1 10 (by decide) (by decide)
                  (.halt true)
                  (.halt false)))))
          (.halt false))
        (.load 1 (.branch .ult 1 8 (by decide) (by decide)
            (.branch .slt 1 5 (by decide) (by decide)
              (.halt false)
              (.load 2 (.branch .eq 2 3 (by decide) (by decide)
                  (.halt false)
                  (.halt true))))
            (.branch .eq 0 9 (by decide) (by decide)
              (.load 2 (.branch .eq 2 3 (by decide) (by decide)
                  (.halt false)
                  (.halt true)))
              (.halt true))))))

theorem eight_program_correct : ∀ i : Fin 128, eval eightProgram i = isCover i := by
  native_decide

/-- This inclusion-minimal witness was found by deleting rows; there may be a
smaller witness elsewhere in the catalog. -/
def witnessRows : List Nat :=
  [26, 27, 29, 46, 47, 58, 77, 82, 87, 88, 90, 91, 92, 93, 102, 104, 110, 114, 120, 122]

def witnessSet : Nat := rowSet fun i => witnessRows.contains i

def witnessAnswer (r : Nat) : Cert (possible 7 0 r) := (cached 7 0 r).run' {}

theorem witness_has_twenty_distinct_rows :
    witnessRows.length = 20 ∧ witnessRows.Nodup ∧ witnessRows.all (· < 128) = true := by
  native_decide

theorem witness_fails_in_seven : ¬ Fits 7 0 witnessSet := by
  rw [fits_iff, ← (witnessAnswer witnessSet).property]
  native_decide

theorem removing_any_witness_row_suffices {j : Nat} (hj : j ∈ witnessRows) :
    Fits 7 0 (second witnessSet (1 <<< j)) := by
  have all_fit : witnessRows.all (fun r => (witnessAnswer (second witnessSet (1 <<< r))).val)
      = true := by native_decide
  rw [fits_iff, ← (witnessAnswer _).property]
  exact List.all_eq_true.mp all_fit j hj

end DirectComparisonSevenCycle
