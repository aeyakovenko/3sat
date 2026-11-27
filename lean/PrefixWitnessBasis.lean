import Std

namespace PrefixWitnessBasis

/-- Apply a query's binary linear functional to a sum of rows. -/
def xorValues {α : Type} (eval : α → Bool) : List α → Bool
  | [] => false
  | row :: rows => (eval row).xor (xorValues eval rows)

theorem oneSummand {α : Type} (eval : α → Bool) (rows : List α)
    (h : xorValues eval rows = true) : ∃ r ∈ rows, eval r = true := by
  induction rows with
  | nil => simp [xorValues] at h
  | cons a rest ih =>
    cases ha : eval a with
    | true => exact ⟨a, List.mem_cons_self, ha⟩
    | false =>
      have hr : xorValues eval rest = true := by
        simpa [xorValues, ha] using h
      obtain ⟨r, hmem, hval⟩ := ih hr
      exact ⟨r, List.mem_cons_of_mem a hmem, hval⟩

theorem savedWitness {α : Type} (eval : α → Bool) (lifetime : α → Nat)
    (a : α) (rows : List α) (t : Nat)
    (representation : xorValues eval rows = eval a)
    (older : ∀ r ∈ rows, lifetime a ≤ lifetime r)
    (passes : eval a = true) (survives : t ≤ lifetime a) :
    ∃ r ∈ rows, eval r = true ∧ t ≤ lifetime r := by
  obtain ⟨r, hmem, hval⟩ := oneSummand eval rows (representation.trans passes)
  exact ⟨r, hmem, hval, Nat.le_trans survives (older r hmem)⟩

/-- When each marked query forces its own data support, a witness answering
two marked queries identifies their indices. -/
theorem incompatibleQueries {A Q : Type} (support : A → Q)
    (answers : A → Q → Prop) (forced : ∀ a q, answers a q → support a = q)
    {a : A} {q r : Q} (hq : answers a q) (hr : answers a r) : q = r :=
  (forced a q hq).symm.trans (forced a r hr)

/-- Parallel completion of any face with exactly one uncolored point. -/
def colored {A Q : Type} (face : Q → A → Prop) (seed : A → Prop) : Nat → A → Prop
  | 0, x => seed x
  | t + 1, x => colored face seed t x ∨
      ∃ q, face q x ∧ ∀ y, face q y → y ≠ x → colored face seed t y

/-- A private pin face at each point's last queried threshold suffices to
color the complement of the starting seed in the stated number of rounds. -/
theorem coveredByLifetime {A Q : Type} (face : Q → A → Prop) (listed : A → Prop)
    (last : A → Nat) (positive : ∀ x, listed x → 0 < last x)
    (isolates : ∀ x, listed x →
        ∃ q, face q x ∧ ∀ y, face q y → y ≠ x → listed y → last y < last x)
    (t : Nat) : ∀ x, (listed x → last x ≤ t) → colored face (fun y => ¬listed y) t x := by
  classical
  induction t with
  | zero =>
    intro x hx hlist
    have := (hx hlist)
    have := positive x hlist
    omega
  | succ t ih =>
    intro x hx
    by_cases early : listed x → last x ≤ t
    · exact Or.inl (ih x early)
    · have hxlist : listed x := Classical.byContradiction (fun h =>
        early (fun hl => (h hl).elim))
      obtain ⟨q, hqx, hq⟩ := isolates x hxlist
      refine Or.inr ⟨q, hqx, ?_⟩
      intro y hqy hne
      exact ih y (fun hyl => by
        have := hq y hqy hne hyl
        have := hx hxlist
        omega)

/-- The face witnessing a first infection is private in the previous
uncolored domain, which gives the reverse witness query. -/
theorem privateAtFirstRound {A Q : Type} (face : Q → A → Prop) (seed : A → Prop)
    (t : Nat) (x : A) (newly : colored face seed (t+1) x)
    (old : ¬colored face seed t x) :
    ∃ q, face q x ∧ ∀ y, face q y → ¬colored face seed t y → y = x := by
  classical
  rcases newly with earlier | ⟨q, hqx, hq⟩
  · exact (old earlier).elim
  · refine ⟨q, hqx, ?_⟩
    intro y hy uncolored
    exact Classical.byContradiction (fun hne => uncolored (hq y hy hne))

end PrefixWitnessBasis
