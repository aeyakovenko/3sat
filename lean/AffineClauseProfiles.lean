import Std

/-! Four occurring variables in first-occurrence order, labeled 00, 01, 10, 11. -/
namespace AffineClauseProfiles

abbrev Assignment := Fin 4 → Bool

/-- The clause uses variables i, j, k and forbids the indicated three bits.
A true bit specifies a negative literal. -/
structure Clause where
  i : Fin 4
  j : Fin 4
  k : Fin 4
  a : Bool
  b : Bool
  c : Bool
  deriving DecidableEq

def Clause.proper (s : Clause) : Bool := s.i != s.j && s.j != s.k && s.k != s.i

def Clause.violated (s : Clause) (x : Assignment) : Bool :=
  x s.i == s.a && x s.j == s.b && x s.k == s.c

def score (formula : List Clause) (x : Assignment) : Nat :=
  (formula.filter (fun s => s.violated x)).length

def positive : List Clause := [
  ⟨0,1,2, false,false,true⟩,
  ⟨0,1,2, false,true,false⟩,
  ⟨0,1,2, false,true,true⟩,
  ⟨0,1,2, true,false,false⟩,
  ⟨0,1,2, true,false,true⟩,
  ⟨0,1,2, true,true,false⟩,
  ⟨0,1,2, true,true,true⟩,
  ⟨0,1,3, false,false,false⟩]

/-- Branch on variable 0. For each branch, forbid all four settings of
variables 1 and 2, or of variables 1 and 3, respectively. -/
def negative : List Clause := [
  ⟨0,1,2, false,false,false⟩,
  ⟨0,1,2, false,false,true⟩,
  ⟨0,1,2, false,true,false⟩,
  ⟨0,1,2, false,true,true⟩,
  ⟨0,1,3, true,false,false⟩,
  ⟨0,1,3, true,false,true⟩,
  ⟨0,1,3, true,true,false⟩,
  ⟨0,1,3, true,true,true⟩]

def labels (formula : List Clause) : List (Fin 4) :=
  (formula.flatMap (fun s => [s.i, s.j, s.k])).eraseDups

theorem exact_syntax :
    positive.length = 8 ∧ negative.length = 8 ∧ positive.Nodup ∧ negative.Nodup ∧
    positive.all Clause.proper = true ∧ negative.all Clause.proper = true ∧
    labels positive = [0,1,2,3] ∧ labels negative = [0,1,2,3] := by decide

def bits (a b c d : Bool) (i : Fin 4) : Bool :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

private theorem expand (x : Assignment) : x = bits (x 0) (x 1) (x 2) (x 3) := by
  funext i
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  | ⟨n + 4, h⟩ => omega

def affine (u v offset : Bool) : Assignment :=
  bits offset (offset ^^ u) (offset ^^ v) (offset ^^ u ^^ v)

theorem affine_profiles :
    ∀ u v offset : Bool,
      score positive (affine u v offset) = 1 ∧ score negative (affine u v offset) = 1 := by
  decide

theorem unique_positive_model (x : Assignment) :
    score positive x = 0 ↔ x = bits false false false true := by
  constructor
  · intro h
    have table : ∀ a b c d : Bool, score positive (bits a b c d) = 0 →
        a = false ∧ b = false ∧ c = false ∧ d = true := by decide
    rw [expand x] at h
    obtain ⟨ha, hb, hc, hd⟩ := table _ _ _ _ h
    exact (expand x).trans (by rw [ha, hb, hc, hd])
  · rintro rfl
    decide

theorem negative_always_one (x : Assignment) : score negative x = 1 := by
  rw [expand x]
  exact (show ∀ a b c d : Bool, score negative (bits a b c d) = 1 by decide) _ _ _ _

theorem negative_unsatisfiable : ¬∃ x, score negative x = 0 := by
  rintro ⟨x, hx⟩
  have h := negative_always_one x
  omega

/-- Sum of the eight scores, including the two constant assignments. -/
def profileSum (f : List Clause) : Nat :=
  score f (affine false false false) + score f (affine false false true) +
  score f (affine false true false) + score f (affine false true true) +
  score f (affine true false false) + score f (affine true false true) +
  score f (affine true true false) + score f (affine true true true)

private theorem add_clause (s : Clause) (f : List Clause) (x : Assignment) :
    score (s :: f) x = score [s] x + score f x := by
  cases h : s.violated x <;> simp [score, h, Nat.add_comm]

private theorem add_profile (s : Clause) (f : List Clause) :
    profileSum (s :: f) = profileSum [s] + profileSum f := by
  simp only [profileSum, add_clause s f]
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem each_clause_hits_one (s : Clause) :
    s.proper = true → profileSum [s] = 1 := by
  have all : ∀ (i j k : Fin 4) (a b c : Bool),
      (Clause.mk i j k a b c).proper = true →
      profileSum [Clause.mk i j k a b c] = 1 := by decide
  cases s
  apply all

theorem sum_of_scores (f : List Clause) (proper : f.all Clause.proper = true) :
    profileSum f = f.length := by
  induction f with
  | nil => rfl
  | cons s f ih =>
    obtain ⟨head, tail⟩ : s.proper = true ∧ f.all Clause.proper = true := by
      simpa using proper
    rw [add_profile, each_clause_hits_one s head, ih tail, List.length_cons]
    omega

/-- Minimality in clause count for every proper formula on these four names. -/
theorem seven_have_affine_model (f : List Clause) (proper : f.all Clause.proper = true)
    (size : f.length ≤ 7) : ∃ u v offset : Bool, score f (affine u v offset) = 0 := by
  by_cases found : ∃ u v offset : Bool, score f (affine u v offset) = 0
  · exact found
  · have misses (u v offset : Bool) : 0 < score f (affine u v offset) := by
      rcases Nat.eq_zero_or_pos (score f (affine u v offset)) with zero | pos
      · exact False.elim (found ⟨u, v, offset, zero⟩)
      · exact pos
    have total := sum_of_scores f proper
    unfold profileSum at total
    have a := misses false false false
    have b := misses false false true
    have c := misses false true false
    have d := misses false true true
    have e := misses true false false
    have g := misses true false true
    have h := misses true true false
    have i := misses true true true
    omega

end AffineClauseProfiles
