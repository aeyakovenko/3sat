import Std

namespace LateClauseLiteralProfiles

structure Literal (ν : Type) where
  var : ν
  sign : Bool

abbrev Clause (ν : Type) := List (Literal ν)
abbrev CNF (ν : Type) := List (Clause ν)
abbrev Assignment (ν : Type) := ν → Bool

variable {ν ι : Type} {r : Nat}

def TrueAt (l : Literal ν) (x : Assignment ν) : Prop := x l.var = l.sign

def Models (x : Assignment ν) (B : CNF ν) : Prop :=
  ∀ c ∈ B, ∃ l ∈ c, TrueAt l x

def Satisfiable (B : CNF ν) : Prop := ∃ x, Models x B

def Occurs (B : CNF ν) (v : ν) : Prop :=
  ∃ c ∈ B, ∃ l ∈ c, l.var = v

def Blocks (B : CNF ν) (x : Assignment ν) (l : Literal ν) : Prop :=
  Occurs B l.var ∧ ¬ TrueAt l x

/-- An extension satisfying the baseline and one chosen literal per query clause
is exactly a model of the concatenated CNF. Duplicate and empty clauses are allowed. -/
theorem sat_append_iff (B : CNF ν) (Q : Fin r → Clause ν) :
    Satisfiable (B ++ List.ofFn Q) ↔
      ∃ (x : Assignment ν) (pick : Fin r → Literal ν),
        Models x B ∧ ∀ k, pick k ∈ Q k ∧ TrueAt (pick k) x := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    have hits (k : Fin r) : ∃ l ∈ Q k, TrueAt l x :=
      hx (Q k) (List.mem_append_right _ (List.mem_ofFn.mpr ⟨k, rfl⟩))
    exact ⟨x, fun k => Classical.choose (hits k),
      fun c hc => hx c (List.mem_append_left _ hc), fun k => Classical.choose_spec (hits k)⟩
  · rintro ⟨x, pick, hb, hp⟩
    refine ⟨x, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact hb c hc
    · obtain ⟨k, hk⟩ := List.mem_ofFn.mp hc
      subst c
      exact ⟨pick k, hp k⟩

/-- A partial assignment on S suffices to establish the baseline if it hits
every baseline clause with a true literal. Any forbidden cross must conflict
on one of those variables, even if the baseline mentions many more. -/
theorem conflict_on_certificate (B : CNF ν) (Q : Fin r → Clause ν)
    (x y : Assignment ν) (pick : Fin r → Literal ν) (S : ν → Prop)
    (cover : ∀ c ∈ B, ∃ l ∈ c, TrueAt l x ∧ S l.var)
    (hp : ∀ k, pick k ∈ Q k ∧ TrueAt (pick k) y)
    (unsat : ¬ Satisfiable (B ++ List.ofFn Q)) :
    ∃ k, S (pick k).var ∧ ¬ TrueAt (pick k) x := by
  classical
  apply Classical.byContradiction
  intro hn
  let z : Assignment ν := fun v => if S v then x v else y v
  apply unsat
  apply (sat_append_iff B Q).mpr
  refine ⟨z, pick, ?_, ?_⟩
  · intro c hc
    obtain ⟨l, hl, htrue, ho⟩ := cover c hc
    exact ⟨l, hl, by simpa [TrueAt, z, ho] using htrue⟩
  · intro k
    refine ⟨(hp k).1, ?_⟩
    by_cases ho : S (pick k).var
    · have ht : TrueAt (pick k) x := Classical.byContradiction
        (fun hfalse => hn ⟨k, ho, hfalse⟩)
      simpa [TrueAt, z, ho] using ht
    · simpa [TrueAt, z, ho] using (hp k).2

/-- Use all variables that actually occur in the baseline as a certificate. -/
theorem conflict_on_baseline (B : CNF ν) (Q : Fin r → Clause ν)
    (x y : Assignment ν) (pick : Fin r → Literal ν) (hb : Models x B)
    (hp : ∀ k, pick k ∈ Q k ∧ TrueAt (pick k) y)
    (unsat : ¬ Satisfiable (B ++ List.ofFn Q)) :
    ∃ k, Blocks B x (pick k) := by
  apply conflict_on_certificate B Q x y pick (Occurs B) _ hp unsat
  intro c hc
  obtain ⟨l, hl, ht⟩ := hb c hc
  exact ⟨l, hl, ht, c, hc, l, hl, rfl⟩

/-- Choosing one satisfied literal per baseline clause makes the conflict
syntactic: two selected occurrences have the same variable and opposite signs. -/
theorem conflicting_chosen_occurrences {b : Nat} (B : Fin b → Clause ν)
    (Q : Fin r → Clause ν) (x y : Assignment ν) (left : Fin b → Literal ν)
    (right : Fin r → Literal ν) (hl : ∀ t, left t ∈ B t ∧ TrueAt (left t) x)
    (hr : ∀ k, right k ∈ Q k ∧ TrueAt (right k) y)
    (unsat : ¬ Satisfiable (List.ofFn B ++ List.ofFn Q)) :
    ∃ t k, (left t).var = (right k).var ∧ (left t).sign ≠ (right k).sign := by
  let S : ν → Prop := fun v => ∃ t, (left t).var = v
  have cover (c) (hc : c ∈ List.ofFn B) : ∃ l ∈ c, TrueAt l x ∧ S l.var := by
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨left t, (hl t).1, (hl t).2, t, rfl⟩
  obtain ⟨k, ⟨t, hv⟩, hbad⟩ :=
    conflict_on_certificate (List.ofFn B) Q x y right S cover hr unsat
  refine ⟨t, k, hv, fun he => hbad ?_⟩
  exact (congrArg x hv).symm.trans (((hl t).2).trans he)

/-- Every diagonal of a SAT identity family supplies a baseline model and
at most r query literals. The baseline's forbidden literals miss its own
choices and meet those of every other query. The same choices work for all
crosses simultaneously. -/
theorem identity_literal_profiles (B : ι → CNF ν) (Q : ι → Fin r → Clause ν)
    (diag : ∀ i, Satisfiable (B i ++ List.ofFn (Q i)))
    (off : ∀ i j, i ≠ j → ¬ Satisfiable (B i ++ List.ofFn (Q j))) :
    ∃ (x : ι → Assignment ν) (pick : ι → Fin r → Literal ν),
      (∀ i, Models (x i) (B i)) ∧
      (∀ i k, pick i k ∈ Q i k ∧ TrueAt (pick i k) (x i)) ∧
      (∀ i k, ¬ Blocks (B i) (x i) (pick i k)) ∧
      (∀ i j, i ≠ j → ∃ k, Blocks (B i) (x i) (pick j k)) := by
  classical
  let diagonalData := fun i => (sat_append_iff (B i) (Q i)).mp (diag i)
  let x := fun i => Classical.choose (diagonalData i)
  let choices := fun i => Classical.choose_spec (diagonalData i)
  let pick := fun i => Classical.choose (choices i)
  have h (i : ι) : Models (x i) (B i) ∧
      ∀ k, pick i k ∈ Q i k ∧ TrueAt (pick i k) (x i) :=
    Classical.choose_spec (choices i)
  refine ⟨x, pick, fun i => (h i).1, fun i => (h i).2, ?_, ?_⟩
  · exact fun i k hblocked => hblocked.2 ((h i).2 k).2
  · exact fun i j hij =>
      conflict_on_baseline (B i) (Q j) (x i) (x j) (pick j)
        (h i).1 (h j).2 (off i j hij)

def Opposite (l m : Literal ν) : Prop := l.var = m.var ∧ l.sign ≠ m.sign

/-- Profiles for any prescribed diagonal-compatible partial implicants. A
certificate is a membership predicate on signed literals, so the elements
counted by its size are distinct. The implication may be semantic. The
same diagonal assignment and query choices work on every cross. -/
theorem identity_implicant_profiles (B : ι → CNF ν) (Q : ι → Fin r → Clause ν)
    (cert : ι → Literal ν → Prop)
    (implicant : ∀ i x, (∀ l, cert i l → TrueAt l x) → Models x (B i))
    (compatible : ∀ i, ∃ x, (∀ l, cert i l → TrueAt l x) ∧
        Models x (List.ofFn (Q i)))
    (off : ∀ i j, i ≠ j → ¬ Satisfiable (B i ++ List.ofFn (Q j))) :
    ∃ (x : ι → Assignment ν) (pick : ι → Fin r → Literal ν),
      (∀ i l, cert i l → TrueAt l (x i)) ∧ (∀ i, Models (x i) (B i)) ∧
      (∀ i k, pick i k ∈ Q i k ∧ TrueAt (pick i k) (x i)) ∧
      (∀ i l k, cert i l → ¬ Opposite l (pick i k)) ∧
      (∀ i j, i ≠ j → ∃ l, cert i l ∧ ∃ k, Opposite l (pick j k)) := by
  classical
  let x := fun i => Classical.choose (compatible i)
  have hx (i : ι) := Classical.choose_spec (compatible i)
  have hits (i : ι) (k : Fin r) : ∃ l ∈ Q i k, TrueAt l (x i) :=
    (hx i).2 (Q i k) (List.mem_ofFn.mpr ⟨k, rfl⟩)
  let pick := fun i k => Classical.choose (hits i k)
  have hp (i : ι) (k : Fin r) : pick i k ∈ Q i k ∧ TrueAt (pick i k) (x i) :=
    Classical.choose_spec (hits i k)
  refine ⟨x, pick, fun i => (hx i).1, fun i => implicant i (x i) (hx i).1, hp, ?_, ?_⟩
  · intro i l k hc hclash
    exact hclash.2 (((hx i).1 l hc).symm.trans
      ((congrArg (x i) hclash.1).trans (hp i k).2))
  · intro i j hij
    apply Classical.byContradiction
    intro hn
    let S : ν → Prop := fun v => ∃ l, cert i l ∧ l.var = v
    let z : Assignment ν := fun v => if S v then x i v else x j v
    apply off i j hij
    apply (sat_append_iff (B i) (Q j)).mpr
    refine ⟨z, pick j, implicant i z ?_, ?_⟩
    · intro l hc
      have hS : S l.var := ⟨l, hc, rfl⟩
      simpa [TrueAt, z, hS] using (hx i).1 l hc
    · intro k
      refine ⟨(hp j k).1, ?_⟩
      by_cases hS : S (pick j k).var
      · obtain ⟨l, hc, hv⟩ := hS
        have he : l.sign = (pick j k).sign :=
          Classical.byContradiction (fun ne => hn ⟨l, hc, k, hv, ne⟩)
        have ht := (congrArg (x i) hv).symm.trans (((hx i).1 l hc).trans he)
        have hs : S (pick j k).var := ⟨l, hc, hv⟩
        simpa [TrueAt, z, hs] using ht
      · simpa [TrueAt, z, hS] using (hp j k).2

end LateClauseLiteralProfiles
