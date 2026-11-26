import Std

/-! A marked type represents a false SAT signature. The algorithm records
one original Horn rule for each fresh mark. A positive leaf that was marked
is the last item of a conflict certificate. No time bound for realizing a
signature or its SAT queries is assumed. -/

namespace SatSignatureConflict

structure Rule (α : Type) where
  body : List α
  head : α
deriving DecidableEq

variable {α : Type} [DecidableEq α]

def heads (trace : List (Rule α)) : List α := trace.map Rule.head

def Closed (rules : List (Rule α)) (mark : α → Prop) : Prop :=
  ∀ r ∈ rules, (∀ x ∈ r.body, mark x) → mark r.head

def Model (rules : List (Rule α)) (positive : List α) (mark : α → Prop) : Prop :=
  Closed rules mark ∧ ∀ x ∈ positive, ¬mark x

/-- Traces are stored in reverse order. The body of a rule has to be justified
by earlier entries, and its head cannot already have occurred. -/
inductive Chain (rules : List (Rule α)) : List (Rule α) → Prop
  | empty : Chain rules []
  | add {r prior} (history : Chain rules prior) (original : r ∈ rules)
      (enabled : ∀ x ∈ r.body, x ∈ heads prior) (fresh : r.head ∉ heads prior) :
      Chain rules (r :: prior)

omit [DecidableEq α] in
theorem Chain.nodup {rules trace : List (Rule α)} (der : Chain rules trace) :
    (heads trace).Nodup := by
  induction der with
  | empty => simp [heads]
  | add _ _ _ fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

omit [DecidableEq α] in
theorem Chain.sound {rules trace : List (Rule α)} (der : Chain rules trace)
    {mark : α → Prop} (closed : Closed rules mark) : ∀ x ∈ heads trace, mark x := by
  induction der with
  | empty => simp [heads]
  | add _ original enabled _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | earlier
    · exact closed _ original (fun a ha => ih a (enabled a ha))
    · exact ih x earlier

def ready (trace : List (Rule α)) (r : Rule α) : Bool :=
  !(heads trace).contains r.head && r.body.all (fun a => (heads trace).contains a)

theorem ready_iff (trace : List (Rule α)) (r : Rule α) :
    ready trace r = true ↔ r.head ∉ heads trace ∧ ∀ x ∈ r.body, x ∈ heads trace := by
  simp [ready, List.all_eq_true, List.contains_iff_mem]

/-- Executable saturation. Fuel counts successful additions, so at most one
scan is needed per available type plus the final unsuccessful scan. -/
def saturate (rules : List (Rule α)) : Nat → List (Rule α) → List (Rule α)
  | 0, trace => trace
  | fuel+1, trace =>
    match rules.find? (ready trace) with
    | none => trace
    | some r => saturate rules fuel (r :: trace)

theorem saturate_chain (rules : List (Rule α)) (fuel : Nat) (trace : List (Rule α))
    (hist : Chain rules trace) :
    Chain rules (saturate rules fuel trace) ∧
      (saturate rules fuel trace).length ≤ trace.length + fuel := by
  induction fuel generalizing trace with
  | zero => exact ⟨hist, by simp [saturate]⟩
  | succ fuel ih =>
    cases found : rules.find? (ready trace) with
    | none => exact ⟨by simpa [saturate, found] using hist, by simp [saturate, found]⟩
    | some r =>
      obtain ⟨fresh, enabled⟩ := (ready_iff trace r).mp (List.find?_some found)
      obtain ⟨chain, bound⟩ :=
        ih (r :: trace) (.add hist (List.mem_of_find?_eq_some found) enabled fresh)
      simp only [saturate, found]
      exact ⟨chain, by simp only [List.length_cons] at bound; omega⟩

/-- An invariant for the finite universe. Each possible head is already
marked or still in the remaining list. Each addition consumes one entry. -/
theorem saturate_closed (rules : List (Rule α)) (fuel : Nat) (trace : List (Rule α))
    (remaining : List α) (enough : remaining.length ≤ fuel)
    (covers : ∀ r ∈ rules, r.head ∈ heads trace ∨ r.head ∈ remaining) :
    Closed rules (fun x => x ∈ heads (saturate rules fuel trace)) := by
  induction fuel generalizing trace remaining with
  | zero =>
    have empty : remaining = [] := List.length_eq_zero_iff.mp (by omega)
    intro r hr _
    simpa [empty, saturate] using covers r hr
  | succ fuel ih =>
    cases found : rules.find? (ready trace) with
    | none =>
      simp only [saturate, found]
      intro r hr body
      by_cases marked : r.head ∈ heads trace
      · exact marked
      · exact False.elim ((List.find?_eq_none.mp found r hr)
          ((ready_iff trace r).mpr ⟨marked, body⟩))
    | some r =>
      obtain ⟨fresh, _⟩ := (ready_iff trace r).mp (List.find?_some found)
      have available : r.head ∈ remaining :=
        (covers r (List.mem_of_find?_eq_some found)).resolve_left fresh
      simp only [saturate, found]
      apply ih (r :: trace) (remaining.erase r.head)
      · rw [List.length_erase_of_mem available]
        omega
      · intro s hs
        by_cases eq : s.head = r.head
        · exact Or.inl (List.mem_cons.mpr (.inl eq))
        · rcases covers s hs with old | future
          · exact Or.inl (List.mem_cons_of_mem _ old)
          · exact Or.inr ((List.mem_erase_of_ne eq).mpr future)

/-- A conflict carries the actual rules and an actual positive leaf. -/
def Conflict (rules : List (Rule α)) (positive : List α)
    (trace : List (Rule α)) (last : α) : Prop :=
  Chain rules trace ∧ last ∈ heads trace ∧ last ∈ positive

omit [DecidableEq α] in
theorem conflict_rules_out_model {rules : List (Rule α)} {positive : List α}
    {trace : List (Rule α)} {last : α} (certificate : Conflict rules positive trace last) :
    ¬∃ mark, Model rules positive mark := by
  obtain ⟨chain, marked, endpoint⟩ := certificate
  rintro ⟨mark, closed, forbidden⟩
  exact forbidden last endpoint (chain.sound closed last marked)

theorem unsat_iff_bounded_conflict (rules : List (Rule α)) (positive types : List α)
    (covers : ∀ r ∈ rules, r.head ∈ types) :
    (¬∃ mark, Model rules positive mark) ↔
      ∃ trace last, Conflict rules positive trace last ∧
        (heads trace).Nodup ∧ trace.length + 1 ≤ types.length + 1 := by
  constructor
  · intro unsat
    let trace := saturate rules types.length []
    have closed : Closed rules (fun x => x ∈ heads trace) :=
      saturate_closed rules _ [] types (Nat.le_refl _)
        (fun r hr => Or.inr (covers r hr))
    obtain ⟨chain, length⟩ := saturate_chain rules types.length [] .empty
    cases hit : positive.find? (fun x => (heads trace).contains x) with
    | none =>
      apply False.elim
      apply unsat ⟨_, closed, ?_⟩
      intro x hx marked
      exact (List.find?_eq_none.mp hit x hx) (List.contains_iff_mem.mpr marked)
    | some last =>
      exact ⟨trace, last, ⟨chain, List.contains_iff_mem.mp (List.find?_some hit),
        List.mem_of_find?_eq_some hit⟩, chain.nodup, by
          change (saturate rules types.length []).length + 1 ≤ types.length + 1
          simp only [List.length_nil, Nat.zero_add] at length
          omega⟩
  · rintro ⟨_, _, cert, _, _⟩
    exact conflict_rules_out_model cert

/-- Each local equation requires a false parent exactly when all children are
false. Empty-premise rules pin false seeds. The true leaves are forbidden
marks. Multiple occurrences can share a type and a parent may be repeated. -/
def equationRules (e : Rule α) : List (Rule α) :=
  e :: e.body.map (fun child => ⟨[e.head], child⟩)

def signatureRules (equations : List (Rule α)) (falseSeeds : List α) : List (Rule α) :=
  falseSeeds.map (fun a => ⟨[], a⟩) ++ equations.flatMap equationRules

def SignatureModel (equations : List (Rule α)) (falseSeeds trueLeaves : List α)
    (mark : α → Prop) : Prop :=
  (∀ x ∈ falseSeeds, mark x) ∧ (∀ x ∈ trueLeaves, ¬mark x) ∧
    ∀ e ∈ equations, mark e.head ↔ ∀ x ∈ e.body, mark x

omit [DecidableEq α] in
theorem signature_model_iff (equations : List (Rule α)) (falseSeeds trueLeaves : List α)
    (mark : α → Prop) :
    SignatureModel equations falseSeeds trueLeaves mark ↔
      Model (signatureRules equations falseSeeds) trueLeaves mark := by
  constructor
  · rintro ⟨seeds, forbid, exactEq⟩
    refine ⟨?_, forbid⟩
    intro r hr allBody
    rcases List.mem_append.mp hr with unit | node
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp unit
      exact seeds a ha
    · obtain ⟨e, he, member⟩ := List.mem_flatMap.mp node
      rcases List.mem_cons.mp member with rfl | backwards
      · exact (exactEq _ he).mpr allBody
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp backwards
        exact (exactEq e he).mp (allBody e.head (by simp)) x hx
  · rintro ⟨closed, forbid⟩
    refine ⟨?_, forbid, ?_⟩
    · intro x hx
      apply closed ⟨[], x⟩
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
      · simp
    · intro e he
      constructor
      · intro parent x hx
        apply closed ⟨[e.head], x⟩
        · apply List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, ?_⟩)
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
        · simpa using parent
      · apply closed e
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_self⟩)

theorem finite_signature_conflict (r : Nat) (equations : List (Rule (Fin r)))
    (falseSeeds trueLeaves : List (Fin r)) :
    (¬∃ mark, SignatureModel equations falseSeeds trueLeaves mark) ↔
      ∃ trace last, Conflict (signatureRules equations falseSeeds) trueLeaves trace last ∧
        (heads trace).Nodup ∧ trace.length + 1 ≤ r + 1 := by
  have bridge : (∃ mark, SignatureModel equations falseSeeds trueLeaves mark) ↔
      (∃ mark, Model (signatureRules equations falseSeeds) trueLeaves mark) :=
    exists_congr (signature_model_iff equations falseSeeds trueLeaves)
  rw [bridge]
  let types := List.finRange r
  have covers : ∀ row ∈ signatureRules equations falseSeeds, row.head ∈ types := by
    intro row _
    simp [types, List.finRange, List.mem_ofFn]
  simpa [types] using
    unsat_iff_bounded_conflict (signatureRules equations falseSeeds) trueLeaves types covers

/-- The same equivalence with literal Boolean SAT truth values rather than a
predicate designating the false types. -/
theorem finite_boolean_signature_conflict (r : Nat) (equations : List (Rule (Fin r)))
    (falseSeeds trueLeaves : List (Fin r)) :
    (¬∃ label : Fin r → Bool,
      SignatureModel equations falseSeeds trueLeaves (fun a => label a = false)) ↔
      ∃ trace last, Conflict (signatureRules equations falseSeeds) trueLeaves trace last ∧
        (heads trace).Nodup ∧ trace.length + 1 ≤ r + 1 := by
  classical
  rw [← finite_signature_conflict]
  constructor
  · rintro noBool ⟨mark, valid⟩
    apply noBool
    refine ⟨fun a => !(decide (mark a)), ?_⟩
    simpa using valid
  · rintro noMarks ⟨label, valid⟩
    exact noMarks ⟨_, valid⟩

/-- A finite binary OR tree with its terminal verdicts. -/
inductive OrTree where
  | leaf (value : Bool)
  | branch (left right : OrTree)

/-- A false terminal starts at one. A true terminal receives the cap. -/
def level (cap : Nat) : OrTree → Nat
  | .leaf false => 1
  | .leaf true => cap
  | .branch left right => min cap (max (level cap left) (level cap right) + 1)

theorem level_le_cap {cap : Nat} (h : 1 ≤ cap) (tree : OrTree) :
    level cap tree ≤ cap := by
  cases tree with
  | leaf v => cases v <;> simp [level, h]
  | branch left right => exact Nat.min_le_left ..

/-- Computing all labels again at a smaller positive cap amounts to applying
the same truncation to the original labels. -/
theorem level_truncate {small large : Nat} (positive : 1 ≤ small)
    (ordered : small ≤ large) (tree : OrTree) :
    level small tree = min small (level large tree) := by
  induction tree with
  | leaf v => cases v <;> simp [level, Nat.min_eq_left ordered, Nat.min_eq_right positive]
  | branch left right ihl ihr =>
    simp only [level, ihl, ihr]
    omega

/-- Local correctness at the root when a level is declared true iff it
strictly exceeds the threshold. -/
def ThresholdFits (cap j : Nat) : OrTree → Prop
  | .leaf value => (j < level cap (.leaf value)) ↔ value = true
  | .branch left right => (j < level cap (.branch left right)) ↔
      (j < level cap left ∨ j < level cap right)

/-- Only this threshold can misclassify the local root constraint. For a
saturated branch with a child already at the cap even this threshold works. -/
def exceptionalThreshold (cap : Nat) : OrTree → Nat
  | .leaf false => 0
  | .leaf true => cap
  | .branch left right => max (level cap left) (level cap right)

theorem defect_only_at_exception {cap j : Nat} (positive : 1 ≤ cap)
    (inRange : j ≤ cap) (tree : OrTree) (bad : ¬ThresholdFits cap j tree) :
    j = exceptionalThreshold cap tree := by
  cases tree with
  | leaf v =>
    cases v <;> simp [ThresholdFits, level, exceptionalThreshold] at * <;> omega
  | branch left right =>
    have hl := level_le_cap positive left
    have hr := level_le_cap positive right
    simp only [ThresholdFits, level, exceptionalThreshold] at *
    omega

theorem two_failing_thresholds_equal {cap i j : Nat} (positive : 1 ≤ cap)
    (hi : i ≤ cap) (hj : j ≤ cap) (tree : OrTree)
    (first : ¬ThresholdFits cap i tree) (second : ¬ThresholdFits cap j tree) :
    i = j :=
  (defect_only_at_exception positive hi tree first).trans
    (defect_only_at_exception positive hj tree second).symm

private theorem length_of_covered {xs ys : List Nat} (distinct : xs.Nodup)
    (covered : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    have present := covered x List.mem_cons_self
    have bound := ih (ys := ys.erase x) tail (by
      intro y member
      have ne : y ≠ x := by rintro rfl; exact fresh member
      exact (List.mem_erase_of_ne ne).mpr (covered y (List.mem_cons_of_mem _ member)))
    rw [List.length_erase_of_mem present] at bound
    have nonempty : ys ≠ [] := by rintro rfl; simp at present
    have pos := List.length_pos_iff.mpr nonempty
    simp only [List.length_cons]
    omega

/-- Any chosen collection of at most cap local root constraints admits a
single common threshold interpretation, including mixed leaf and branch roots. -/
theorem common_threshold_for_small_sample {cap : Nat} (positive : 1 ≤ cap)
    (roots : List OrTree) (budget : roots.length ≤ cap) :
    ∃ j ≤ cap, ∀ t ∈ roots, ThresholdFits cap j t := by
  classical
  apply Classical.byContradiction
  intro noGood
  have covered : ∀ j ∈ List.range (cap + 1), j ∈ roots.map (exceptionalThreshold cap) := by
    intro j mem
    have inRange : j ≤ cap := by have := List.mem_range.mp mem; omega
    apply Classical.byContradiction
    intro absent
    apply noGood
    refine ⟨j, inRange, ?_⟩
    intro t membership
    apply Classical.byContradiction
    intro bad
    exact absent (List.mem_map.mpr ⟨t, membership,
      (defect_only_at_exception positive inRange t bad).symm⟩)
  have impossible := length_of_covered List.nodup_range covered
  simp only [List.length_range, List.length_map] at impossible
  omega

end SatSignatureConflict
