import Std

namespace ThreeFileCensus

/-- A Boolean label factors through the feature vector on a tail exactly
    when no two points of the tail with equal features have opposite labels.
    With a finite feature type the resulting map is a finite truth table. -/
theorem lookup_iff {X S : Type} (onTail : X → Prop) (feature : X → S) (label : X → Bool) :
    (∃ table : S → Bool, ∀ x, onTail x → table (feature x) = label x) ↔
    (∀ x y, onTail x → onTail y → feature x = feature y → label x = label y) := by
  classical
  constructor
  · rintro ⟨table, h⟩ x y hx hy eq
    rw [← h x hx, ← h y hy, eq]
  · intro consistent
    let table (s : S) : Bool := decide (∃ x, onTail x ∧ feature x = s ∧ label x = true)
    refine ⟨table, ?_⟩
    intro x hx
    cases hl : label x with
    | true =>
      have h : ∃ y, onTail y ∧ feature y = feature x ∧ label y = true := ⟨x,hx,rfl,hl⟩
      simp [table, h]
    | false =>
      have h : ¬ ∃ y, onTail y ∧ feature y = feature x ∧ label y = true := by
        rintro ⟨y,hy,eq,yes⟩
        have bad := consistent y x hy hx eq
        simp_all
      simp [table, h]

/-- Infinitely far collisions from a finite set of signatures have one
    single signature witnessing collisions arbitrarily far out. -/
theorem cofinal_class {S : Type} (occurs : S → Nat → Prop)
    (shrink : ∀ s m n, m ≤ n → occurs s n → occurs s m) (classes : List S)
    (collides : ∀ n, ∃ s ∈ classes, occurs s n) :
    ∃ s ∈ classes, ∀ n, occurs s n := by
  classical
  induction classes with
  | nil =>
    obtain ⟨s,hs,_⟩ := collides 0
    simp at hs
  | cons head tail ih =>
    by_cases good : ∀ n, occurs head n
    · exact ⟨head, by simp, good⟩
    · obtain ⟨bound,hbound⟩ := Classical.not_forall.mp good
      have smaller : ∀ n, ∃ s ∈ tail, occurs s n := by
        intro n
        obtain ⟨s,mem,hs⟩ := collides (max n bound)
        rcases List.mem_cons.mp mem with e | inside
        · subst s
          exact False.elim (hbound (shrink _ _ _ (Nat.le_max_right _ _) hs))
        · exact ⟨s, inside, shrink _ _ _ (Nat.le_max_left _ _) hs⟩
      obtain ⟨s,hs,h⟩ := ih smaller
      exact ⟨s, by simp [hs], h⟩

/-- If no tail is correctly labelled by a lookup on these features, some
    fixed signature occurs on arbitrarily large opposite-labelled inputs. -/
theorem persistent_collision {X S : Type} (size : X → Nat) (feature : X → S) (label : X → Bool)
    (classes : List S) (cover : ∀ x, feature x ∈ classes)
    (noTable : ∀ n, ¬ ∃ tab : S → Bool, ∀ x, n ≤ size x → tab (feature x) = label x) :
    ∃ s ∈ classes, ∀ n, ∃ x y, n ≤ size x ∧ n ≤ size y ∧
      feature x = s ∧ feature y = s ∧ label x ≠ label y := by
  classical
  apply cofinal_class (fun s n => ∃ x y, n ≤ size x ∧ n ≤ size y ∧
    feature x = s ∧ feature y = s ∧ label x ≠ label y) _ classes
  · intro n
    apply Classical.byContradiction
    intro noCollision
    apply noTable n
    apply (lookup_iff (fun x => n ≤ size x) feature label).mpr
    intro x y hx hy eq
    apply Classical.byContradiction
    intro diff
    exact noCollision ⟨feature x, cover x, x, y, hx, hy, rfl, eq.symm, diff⟩
  · intro s m n le
    rintro ⟨x,y,hx,hy,ex,ey,op⟩
    exact ⟨x,y,Nat.le_trans le hx,Nat.le_trans le hy,ex,ey,op⟩

/-- A parameter passing the anchor must agree across lengths with a finite
    representative. A single collision on the entire representative vector
    then refutes each parameter at one of the three displayed files. -/
theorem three_files {P I X : Type} (eval : P → X → Option Bool)
    (probe : I → X → Option Bool) (label : X → Bool) (anchor x y : X)
    (covered : ∀ p, eval p anchor = some (label anchor) →
      ∃ i, ∀ z, eval p z = probe i z)
    (same : ∀ i, probe i x = probe i y) (opposite : label x ≠ label y) :
    ∀ p, ∃ z ∈ [anchor,x,y], eval p z ≠ some (label z) := by
  intro p
  by_cases ha : eval p anchor = some (label anchor)
  · obtain ⟨i, h⟩ := covered p ha
    by_cases hx : eval p x = some (label x)
    · refine ⟨y, by simp, ?_⟩
      intro hy
      apply opposite
      exact Option.some.inj (hx.symm.trans ((h x).trans ((same i).trans ((h y).symm.trans hy))))
    · exact ⟨x, by simp, hx⟩
  · exact ⟨anchor, by simp, ha⟩

private theorem bit_partition {α : Type} (test : α → Bool) (xs : List α) :
    (xs.filter (fun x => test x == false)).length +
    (xs.filter (fun x => test x == true)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : test x <;> simp_all <;> omega

/-- In a binary matrix with t rows at most 2^t columns can be mutually
    distinguishable. Split the columns by the first row and count recursively. -/
theorem separated_columns {R C : Type} (entry : R → C → Bool) (rows : List R)
    (cols : List C)
    (sep : cols.Pairwise (fun x y => ∃ r ∈ rows, entry r x ≠ entry r y)) :
    cols.length ≤ 2^rows.length := by
  induction rows generalizing cols with
  | nil =>
    cases cols with
    | nil => simp
    | cons x xs =>
      cases xs with
      | nil => simp
      | cons y ys =>
        obtain ⟨r,mem,_⟩ := (List.pairwise_cons.mp sep).1 y (by simp)
        cases mem
  | cons head tail ih =>
    have smaller (bit : Bool) :
        (cols.filter (fun x => entry head x == bit)).length ≤ 2^tail.length := by
      apply ih
      apply (sep.filter (fun x => entry head x == bit)).imp_of_mem
      intro x y hx hy h
      obtain ⟨r,mem,diff⟩ := h
      rcases List.mem_cons.mp mem with eq | inside
      · subst r
        have left : entry head x = bit := beq_iff_eq.mp (List.mem_filter.mp hx).2
        have right : entry head y = bit := beq_iff_eq.mp (List.mem_filter.mp hy).2
        exact False.elim (diff (left.trans right.symm))
      · exact ⟨r,inside,diff⟩
    have cnt := bit_partition (entry head) cols
    have a := smaller false
    have b := smaller true
    simp only [List.length_cons, Nat.pow_succ]
    omega

/-- For each bit pattern on the fixed columns, the matching rows must
    separate every two remaining columns. Thus, for each 2^j strictly
    below the remaining column count, there are at least 2^t*(j+1) rows,
    where t is the number of fixed columns. Taking the largest such j
    gives the rounded base-two logarithmic bound whenever at least two
    columns remain. No enumeration or multiplicity conventions are implicit. -/
theorem covering_matrix_bound {R C : Type} (entry : R → C → Bool)
    (fixed other : List C) (rows : List R) (j : Nat) (many : 2^j < other.length)
    (covers : ∀ pattern : List Bool, pattern.length = fixed.length →
      other.Pairwise fun x y => ∃ r ∈ rows,
        fixed.map (entry r) = pattern ∧ entry r x ≠ entry r y) :
    2^fixed.length*(j+1) ≤ rows.length := by
  induction fixed generalizing rows with
  | nil =>
    have cov := covers [] rfl
    have cap := separated_columns entry rows other (cov.imp (by
      rintro x y ⟨r,hr,_,diff⟩
      exact ⟨r,hr,diff⟩))
    simp
    by_cases h : rows.length ≤ j
    · have contradicts := Nat.pow_le_pow_right Nat.zero_lt_two h
      omega
    · omega
  | cons head tail ih =>
    have forBit (b : Bool) :
        2^tail.length*(j+1) ≤ (rows.filter (fun r => entry r head == b)).length := by
      apply ih
      intro pat len
      apply (covers (b::pat) (by simp [len])).imp
      rintro x y ⟨r,mem,pattern,diff⟩
      obtain ⟨first,rest⟩ := List.cons.inj pattern
      exact ⟨r, List.mem_filter.mpr ⟨mem, beq_iff_eq.mpr first⟩, rest, diff⟩
    have both := Nat.add_le_add (forBit false) (forBit true)
    rw [bit_partition (fun r => entry r head) rows] at both
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      Nat.mul_add, Nat.add_mul, Nat.mul_two, Nat.two_mul] using both

end ThreeFileCensus
