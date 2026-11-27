import Std

namespace GatherMismatch

/-- A table entry, a comparison row, and a chunk value have separate variable banks. -/
inductive Var (I J B D : Type) where
  | selected : I → Var I J B D
  | test : J → B → Var I J B D
  | mark : B → D → Var I J B D

inductive Clause (V : Type) where
  | imply : V → V → Clause V
  | forbid : V → V → Clause V
  | choose : List V → Clause V

def Holds (a : V → Prop) : Clause V → Prop
  | .imply u v => a u → a v
  | .forbid u v => a u → ¬a v
  | .choose choices => ∃ v ∈ choices, a v

/-- Characterizes the clauses before expanding the one disjunction. The row
    lists may contain repetitions. Only queries into present data rows are allowed. -/
def Encodes (rows : List I) (tests : List (J × B)) (banks : List B)
    (x : I → B → D) (q : J → I) (c : J → B → D) (a : Var I J B D → Prop) : Prop :=
  (∀ i ∈ rows, ∀ b ∈ banks, Holds a (.imply (.selected i) (.mark b (x i b)))) ∧
  (∀ p ∈ tests, Holds a (.imply (.test p.1 p.2) (.selected (q p.1))) ∧
                Holds a (.forbid (.test p.1 p.2) (.mark p.2 (c p.1 p.2)))) ∧
  Holds a (.choose (tests.map fun p => .test p.1 p.2))

theorem exists_assignment_iff_mismatch (rows : List I) (tests : List (J × B)) (banks : List B)
    (x : I → B → D) (q : J → I) (c : J → B → D)
    (addressed : ∀ p ∈ tests, q p.1 ∈ rows ∧ p.2 ∈ banks) :
    (∃ a, Encodes rows tests banks x q c a) ↔ ∃ p ∈ tests, x (q p.1) p.2 ≠ c p.1 p.2 := by
  constructor
  · rintro ⟨a, data, query, v, hv, chosen⟩
    obtain ⟨⟨j,b⟩, hp, rfl⟩ := List.mem_map.mp hv
    have selected := (query (j,b) hp).1 chosen
    have yes := data (q j) (addressed (j,b) hp).1 b (addressed (j,b) hp).2 selected
    have no := (query (j,b) hp).2 chosen
    exact ⟨(j,b), hp, fun eq => no (eq ▸ yes)⟩
  · rintro ⟨⟨j,b⟩, hp, mismatch⟩
    let a : Var I J B D → Prop
      | .selected i => i = q j
      | .test l h => l = j ∧ h = b
      | .mark h d => d = x (q j) h
    refine ⟨a, ?_, ?_, ?_⟩
    · intro i _ h _ selected
      change i = q j at selected
      subst i
      rfl
    · rintro ⟨l,h⟩ _
      constructor
      · rintro ⟨rfl, rfl⟩
        rfl
      · rintro ⟨rfl, rfl⟩ eq
        exact mismatch eq.symm
    · exact ⟨.test j b, List.mem_map.mpr ⟨(j,b),hp,rfl⟩, rfl, rfl⟩

/-- With an asserted first prefix and false final prefix, each row here is
    the ternary clause ¬live_i ∨ flag_i ∨ live_(i+1). -/
def ChoiceChain (f : Nat → Prop) (n : Nat) (live : Nat → Prop) : Prop :=
  live 0 ∧ (∀ i < n, live i → f i ∨ live (i+1)) ∧ ¬live n

theorem choice_chain_iff (f : Nat → Prop) (n : Nat) :
    (∃ live, ChoiceChain f n live) ↔ ∃ i < n, f i := by
  classical
  constructor
  · rintro ⟨live, start, step, stop⟩
    apply Classical.byContradiction
    intro none
    have persist (i : Nat) (hi : i ≤ n) : live i := by
      induction i with
      | zero => exact start
      | succ i ih =>
        exact (step i (by omega) (ih (by omega))).resolve_left (fun h => none ⟨i, by omega, h⟩)
    exact stop (persist n (by omega))
  · rintro ⟨j,hj,hit⟩
    refine ⟨fun i => i ≤ j, by omega, ?_, by omega⟩
    intro i _ active
    by_cases e : i = j
    · exact Or.inl (e ▸ hit)
    · exact Or.inr (by omega)

/-- Comparing both polarities of the same bounded word tests equality. -/
theorem double_threshold_iff (maxValue x c : Nat) (hx : x ≤ maxValue) (hc : c ≤ maxValue) :
    (x ≤ c ∧ maxValue-x ≤ maxValue-c) ↔ x = c := by omega

end GatherMismatch
