import Std

namespace ChartChallengeIntersections

abbrev Literal (α : Type) := α × Bool
abbrev Clause (α : Type) := List (Literal α)
abbrev CNF (α : Type) := List (Clause α)

def Accepts (word : α → Bool) (test : CNF α) : Prop :=
  ∀ clause ∈ test, ∃ lit ∈ clause, word lit.1 = lit.2

def WidthAtMost (k : Nat) (test : CNF α) : Prop :=
  ∀ clause ∈ test, clause.length ≤ k

/-- Intersecting any finite collection of tests concatenates its clauses. -/
theorem intersection_accepts (word : α → Bool) (tests : List (CNF α)) :
    Accepts word tests.flatten ↔ ∀ test ∈ tests, Accepts word test := by
  constructor
  · intro accepted test member clause belongs
    exact accepted clause (List.mem_flatten.mpr ⟨test, member, belongs⟩)
  · intro accepted clause belongs
    obtain ⟨test, member, inside⟩ := List.mem_flatten.mp belongs
    exact accepted test member clause inside

theorem intersection_width (k : Nat) (tests : List (CNF α))
    (narrow : ∀ test ∈ tests, WidthAtMost k test) :
    WidthAtMost k tests.flatten := by
  intro clause belongs
  obtain ⟨test, member, inside⟩ := List.mem_flatten.mp belongs
  exact narrow test member clause inside

inductive Challenge (α : Type) where
  | stop (answer : Bool)
  | query (slot : α) (no yes : Challenge α)

def evaluate (word : α → Bool) : Challenge α → Bool
  | .stop b => b
  | .query slot no yes => if word slot then evaluate word yes else evaluate word no

def observed (word : α → Bool) : Challenge α → List α
  | .stop _ => []
  | .query slot no yes =>
      slot :: (if word slot then observed word yes else observed word no)

/-- The answer on one adaptive path persists on its entire agreement cylinder. -/
theorem path_agreement (x y : α → Bool) (test : Challenge α)
    (agree : ∀ slot ∈ observed x test, x slot = y slot) :
    evaluate x test = evaluate y test := by
  induction test with
  | stop => rfl
  | query slot no yes ihNo ihYes =>
    have root : x slot = y slot := agree slot (List.mem_cons_self)
    cases branch : x slot with
    | false =>
      simp only [evaluate, ← root, branch, Bool.false_eq_true, if_false]
      apply ihNo
      intro i inside
      exact agree i (by simpa only [observed, branch, Bool.false_eq_true, if_false]
                            using List.mem_cons_of_mem slot inside)
    | true =>
      simp only [evaluate, ← root, branch, if_true]
      apply ihYes
      intro i inside
      exact agree i (by simpa only [observed, branch, if_true]
                            using List.mem_cons_of_mem slot inside)

def depth : Challenge α → Nat
  | .stop _ => 0
  | .query _ no yes => max (depth no) (depth yes) + 1

def guardClauses (lit : Literal α) (test : CNF α) : CNF α :=
  test.map (fun clause => lit :: clause)

def compile : Challenge α → CNF α
  | .stop true => []
  | .stop false => [[]]
  | .query slot no yes =>
    guardClauses (slot, true) (compile no) ++ guardClauses (slot, false) (compile yes)

private theorem accepts_guard (word : α → Bool) (lit : Literal α) (test : CNF α) :
    Accepts word (guardClauses lit test) ↔ word lit.1 = lit.2 ∨ Accepts word test := by
  constructor
  · intro accepted
    by_cases hit : word lit.1 = lit.2
    · exact Or.inl hit
    · right
      intro clause inside
      obtain ⟨v, whereAt, trueLit⟩ := accepted (lit :: clause) (List.mem_map.mpr ⟨clause, inside, rfl⟩)
      rcases List.mem_cons.mp whereAt with eq | member
      · subst v
        exact (hit trueLit).elim
      · exact ⟨v, member, trueLit⟩
  · intro h clause inside
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp inside
    rcases h with hit | accepted
    · exact ⟨lit, List.mem_cons_self, hit⟩
    · obtain ⟨v, used, trueLit⟩ := accepted old member
      exact ⟨v, List.mem_cons_of_mem lit used, trueLit⟩

/-- Every adaptive depth-k challenge has an equivalent CNF on the same coordinates. -/
theorem compile_correct (word : α → Bool) (test : Challenge α) :
    Accepts word (compile test) ↔ evaluate word test = true := by
  induction test with
  | stop b => cases b <;> simp [compile, Accepts, evaluate]
  | query slot no yes ihNo ihYes =>
    have append (l r : CNF α) : Accepts word (l ++ r) ↔ Accepts word l ∧ Accepts word r := by
      constructor
      · intro accepted
        exact ⟨fun c hc => accepted c (List.mem_append.mpr (.inl hc)),
               fun c hc => accepted c (List.mem_append.mpr (.inr hc))⟩
      · rintro ⟨hl, hr⟩ c hc
        exact (List.mem_append.mp hc).elim (hl c) (hr c)
    cases h : word slot <;> simp [compile, append, accepts_guard, h, ihNo, ihYes, evaluate]

theorem compile_width (test : Challenge α) : WidthAtMost (depth test) (compile test) := by
  induction test with
  | stop b => cases b <;> simp [WidthAtMost, depth, compile]
  | query slot no yes ihNo ihYes =>
    intro clause belongs
    simp only [compile, List.mem_append, guardClauses, List.mem_map] at belongs
    rcases belongs with ⟨c, inside, rfl⟩ | ⟨c, inside, rfl⟩
    · exact Nat.succ_le_succ (Nat.le_trans (ihNo c inside) (Nat.le_max_left _ _))
    · exact Nat.succ_le_succ (Nat.le_trans (ihYes c inside) (Nat.le_max_right _ _))

/-- A finite survey of adaptive challenges only pays their largest query depth in CNF width. -/
theorem survey (tests : List (Challenge α)) (k : Nat) (bounded : ∀ t ∈ tests, depth t ≤ k) :
    ∃ form : CNF α, WidthAtMost k form ∧
      ∀ word, Accepts word form ↔ ∀ t ∈ tests, evaluate word t = true := by
  refine ⟨(tests.map compile).flatten, ?_, ?_⟩
  · apply intersection_width
    intro form inside
    obtain ⟨t, belongs, rfl⟩ := List.mem_map.mp inside
    exact fun c hc => Nat.le_trans (compile_width t c hc) (bounded t belongs)
  · intro word
    rw [intersection_accepts]
    constructor
    · intro accepted t belongs
      exact (compile_correct word t).mp (accepted (compile t) (List.mem_map.mpr ⟨t, belongs, rfl⟩))
    · intro good form inside
      obtain ⟨t, belongs, rfl⟩ := List.mem_map.mp inside
      exact (compile_correct word t).mpr (good t belongs)

/-- Product of the integer signs attached to an ordered tuple, with repetitions. -/
def characterProduct (χ : α → Int) : List α → Int
  | [] => 1
  | x :: xs => χ x * characterProduct χ xs

/-- If translating each point multiplies a character by the same binary sign,
    that sign cancels in the product on every even list. -/
theorem even_translate (χ : α → Int) (shift : α → α) (factor : Int)
    (binary : factor = 1 ∨ factor = -1) (translate : ∀ x, χ (shift x) = factor * χ x) :
    ∀ xs : List α, xs.length % 2 = 0 →
      characterProduct χ (xs.map shift) = characterProduct χ xs
  | [], _ => rfl
  | [_], h => by simp at h
  | x :: y :: xs, h => by
    have tail : xs.length % 2 = 0 := by
      simp only [List.length_cons] at h
      omega
    have square : factor * factor = 1 := by
      rcases binary with one | negOne <;> simp [*]
    simp only [List.map_cons, characterProduct, translate, even_translate χ shift factor binary translate xs tail]
    calc
      _ = (factor * factor) * (χ x * (χ y * characterProduct χ xs)) := by ac_rfl
      _ = _ := by rw [square, Int.one_mul]

end ChartChallengeIntersections
