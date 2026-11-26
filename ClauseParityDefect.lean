import Std

namespace ClauseParityDefect

def sign (b : Bool) : Int := if b then -1 else 1

def oddParity (x y z : Bool) := (x ^^ y) ^^ z

/-- Sum of the three singleton and three pair characters of a satisfied clause. -/
theorem six_characters (x y z : Bool) (sat : (x || y || z) = true) :
    sign x + sign y + sign z + sign x * sign y + sign y * sign z + sign z * sign x =
      (if oddParity x y z then 0 else -2) := by
  cases x <;> cases y <;> cases z <;> first | contradiction | decide

/-- If the bond bit is false the state must stay fixed. -/
def Walk (start stop : Bool) : List Bool → Prop
  | [] => start = stop
  | p :: ps => ∃ next : Bool, (p = true ∨ start = next) ∧ Walk next stop ps

theorem endpoints (ps : List Bool) (a b : Bool) :
    Walk a b ps ↔ a = b ∨ true ∈ ps := by
  induction ps generalizing a b with
  | nil => simp [Walk]
  | cons p ps ih =>
    constructor
    · rintro ⟨next, hp, htail⟩
      rcases hp with hp | hsame
      · subst p
        simp
      · subst next
        rcases (ih a b).mp htail with heq | hmem
        · exact Or.inl heq
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
    · intro h
      rcases h with heq | hmem
      · exact ⟨a, Or.inr rfl, (ih a b).mpr (Or.inl heq)⟩
      · rcases List.mem_cons.mp hmem with hp | htail
        · exact ⟨b, Or.inl hp.symm, (ih b b).mpr (Or.inl rfl)⟩
        · exact ⟨a, Or.inr rfl, (ih a b).mpr (Or.inr htail)⟩

theorem twisted_cycle (ps : List Bool) (a : Bool) :
    Walk a (!a) ps ↔ true ∈ ps := by
  rw [endpoints]
  cases a <;> simp

theorem sign_link (l a b : Bool) :
    ((l || !a || b) && (l || a || !b) = true) ↔ (l = true ∨ a = b) := by
  cases l <;> cases a <;> cases b <;> decide

/-- With equal-mass samples, a strict upper bound on the average produces a good sample. -/
theorem low_sample (counts : List Nat) (k : Nat)
    (h : counts.sum < (k + 1) * counts.length) :
    ∃ n ∈ counts, n ≤ k := by
  induction counts with
  | nil => simp at h
  | cons n ns ih =>
    by_cases small : n ≤ k
    · exact ⟨n, by simp, small⟩
    · simp only [List.sum_cons, List.length_cons, Nat.mul_succ] at h
      have htail : ns.sum < (k + 1) * ns.length := by omega
      obtain ⟨v, hv, hk⟩ := ih htail
      exact ⟨v, List.mem_cons_of_mem _ hv, hk⟩

/-- Three signed literals evaluated on assignments of the same type. -/
structure EvaluatedClause (A : Type) where
  left : A → Bool
  middle : A → Bool
  right : A → Bool

def signedSum {A : Type} (samples : List A) (f : A → Int) : Int :=
  (samples.map f).sum

def clauseDefect {A : Type} (c : EvaluatedClause A) (a : A) : Nat :=
  if oddParity (c.left a) (c.middle a) (c.right a) then 0 else 1

def defects {A : Type} (clauses : List (EvaluatedClause A)) (a : A) : Nat :=
  (clauses.map (fun c => clauseDefect c a)).sum

/-- Unnormalized moment conditions on an equal-mass sample list. Repeated
    assignments are allowed, so integer multiplicities encode rational weights. -/
structure SampleMoments {A : Type} (c : EvaluatedClause A) (samples : List A)
    (B : Nat) : Prop where
  satisfied : ∀ a ∈ samples, (c.left a || c.middle a || c.right a) = true
  left_zero : signedSum samples (fun a => sign (c.left a)) = 0
  middle_zero : signedSum samples (fun a => sign (c.middle a)) = 0
  right_zero : signedSum samples (fun a => sign (c.right a)) = 0
  left_middle : -(B : Int) ≤ signedSum samples (fun a => sign (c.left a) * sign (c.middle a))
  middle_right : -(B : Int) ≤ signedSum samples (fun a => sign (c.middle a) * sign (c.right a))
  right_left : -(B : Int) ≤ signedSum samples (fun a => sign (c.right a) * sign (c.left a))

private theorem sum_clause_identity {A : Type} (c : EvaluatedClause A) (samples : List A)
    (sat : ∀ a ∈ samples, (c.left a || c.middle a || c.right a) = true) :
    signedSum samples (fun a => sign (c.left a)) +
    signedSum samples (fun a => sign (c.middle a)) +
    signedSum samples (fun a => sign (c.right a)) +
    signedSum samples (fun a => sign (c.left a) * sign (c.middle a)) +
    signedSum samples (fun a => sign (c.middle a) * sign (c.right a)) +
    signedSum samples (fun a => sign (c.right a) * sign (c.left a)) +
    2 * ((samples.map (clauseDefect c)).sum : Int) = 0 := by
  induction samples with
  | nil => simp [signedSum]
  | cons a tail ih =>
    have tail_id := ih (fun x hx => sat x (List.mem_cons_of_mem _ hx))
    have point := six_characters (c.left a) (c.middle a) (c.right a) (sat a (by simp))
    simp only [signedSum, List.map_cons, List.sum_cons, Int.natCast_add] at *
    cases hp : oddParity (c.left a) (c.middle a) (c.right a) <;>
      simp only [clauseDefect, hp, Bool.false_eq_true, ↓reduceIte,
        Int.natCast_zero, Int.natCast_one] at * <;> omega

private theorem one_clause_bound {A : Type} (c : EvaluatedClause A) (samples : List A)
    (B : Nat) (h : SampleMoments c samples B) :
    2 * (samples.map (clauseDefect c)).sum ≤ 3 * B := by
  obtain ⟨sat, left0, middle0, right0, lm, mr, rl⟩ := h
  have ident := sum_clause_identity c samples sat
  omega

private theorem total_cons {A : Type} (c : EvaluatedClause A)
    (clauses : List (EvaluatedClause A)) (samples : List A) :
    (samples.map (defects (c :: clauses))).sum =
    (samples.map (clauseDefect c)).sum + (samples.map (defects clauses)).sum := by
  induction samples with
  | nil => simp
  | cons a tail ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp [defects, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Twice the number of defects over all sampled assignments, counting repeats,
    is bounded by three times the number of clauses times the pair-sum budget. -/
theorem formula_defect_bound {A : Type} (clauses : List (EvaluatedClause A))
    (samples : List A) (B : Nat) (h : ∀ c ∈ clauses, SampleMoments c samples B) :
    2 * (samples.map (defects clauses)).sum ≤ 3 * clauses.length * B := by
  induction clauses with
  | nil =>
    have zero : (samples.map (defects ([] : List (EvaluatedClause A)))).sum = 0 := by
      clear h
      induction samples with
      | nil => rfl
      | cons a tail ih => simp [ih, defects]
    simp [zero]
  | cons c tail ih =>
    have headBound := one_clause_bound c samples B (h c (by simp))
    have tailBound := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    rw [total_cons, List.length_cons, Nat.mul_succ, Nat.add_mul]
    omega

/-- A strict average threshold produces an actual member of the sample
    list whose assignment has at most k even-parity clauses. -/
theorem exists_low_defect_assignment {A : Type} (clauses : List (EvaluatedClause A))
    (samples : List A) (B k : Nat) (h : ∀ c ∈ clauses, SampleMoments c samples B)
    (small : 3 * clauses.length * B < 2 * ((k + 1) * samples.length)) :
    ∃ a ∈ samples, defects clauses a ≤ k := by
  have bound := formula_defect_bound clauses samples B h
  have avg : (samples.map (defects clauses)).sum <
      (k + 1) * (samples.map (defects clauses)).length := by
    rw [List.length_map]
    omega
  obtain ⟨v, hv, hk⟩ := low_sample _ k avg
  obtain ⟨a, ha, eq⟩ := List.mem_map.mp hv
  exact ⟨a, ha, eq ▸ hk⟩

/-- The interval between two distinct stored states in a three-layer cycle
cannot contain all or none of every share group. -/
theorem interval_splits_group (groups lo hi : Nat) (g : 0 < groups)
    (order : lo < hi) (bound : hi < 3 * groups) :
    ¬ (∀ i, i + groups < 3 * groups →
      ((lo ≤ i ∧ i < hi) ↔ (lo ≤ i + groups ∧ i + groups < hi))) := by
  intro periodic
  by_cases first : groups ≤ lo
  · have prev := periodic (lo - groups) (by omega)
    have inside := prev.mpr (by omega)
    omega
  · have mid := (periodic lo (by omega)).mp (by omega)
    have last := (periodic (lo + groups) (by omega)).mp (by omega)
    have edge := (periodic (hi - groups) (by omega)).mp (by omega)
    omega

end ClauseParityDefect
