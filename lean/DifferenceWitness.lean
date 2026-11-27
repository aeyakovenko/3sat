import Std

namespace DifferenceWitness

abbrev Edge := Nat → Bool → Nat → Prop

inductive Walk (e : Edge) : Nat → Bool → Nat → Prop where
  | stop (v) : Walk e v false v
  | more {v a u b w} : e v a u → Walk e u b w → Walk e v (a ^^ b) w

theorem Walk.append (first : Walk e v a u) (second : Walk e u b w) :
    Walk e v (a ^^ b) w := by
  induction first with
  | stop => simpa using second
  | more h _ ih =>
    rw [Bool.xor_assoc]
    exact .more h (ih second)

def Sink (e : Edge) (v : Nat) : Prop := ∀ a u, ¬ e v a u

def Ends (e : Edge) (v : Nat) (b : Bool) : Prop := ∃ u, Walk e v b u ∧ Sink e u

def Descends (e : Edge) : Prop := ∀ {v a u}, e v a u → u < v

/-- Each pair of outgoing edges has a common continuation with equal total XOR. -/
def Joins (e : Edge) : Prop :=
  ∀ {v a u b w}, e v a u → e v b w →
    ∃ z i j, Walk e u i z ∧ Walk e w j z ∧ (a ^^ i) = (b ^^ j)

theorem some_end (down : Descends e) (v : Nat) : ∃ b, Ends e v b := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases step : ∃ a u, e v a u
    · obtain ⟨a, u, edge⟩ := step
      obtain ⟨b, w, path, finish⟩ := ih u (down edge)
      exact ⟨_, w, .more edge path, finish⟩
    · exact ⟨false, v, .stop _, fun a u edge => step ⟨a, u, edge⟩⟩

theorem unique_end (down : Descends e) (join : Joins e) (v : Nat) :
    ∀ a b, Ends e v a → Ends e v b → a = b := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    rintro _ _ ⟨_, p, sp⟩ ⟨_, q, sq⟩
    cases p with
    | stop =>
      cases q with
      | stop => rfl
      | more edge _ => exact False.elim (sp _ _ edge)
    | more left pathL =>
      cases q with
      | stop => exact False.elim (sq _ _ left)
      | more right pathR =>
        obtain ⟨z, i, j, ljoin, rjoin, same⟩ := join left right
        obtain ⟨b, t, tail, final⟩ := some_end (e := e) down z
        have eqL := ih _ (down left) _ _ ⟨_, pathL, sp⟩ ⟨t, ljoin.append tail, final⟩
        have eqR := ih _ (down right) _ _ ⟨_, pathR, sq⟩ ⟨t, rjoin.append tail, final⟩
        rw [eqL, eqR, ← Bool.xor_assoc, ← Bool.xor_assoc, same]

/-- The potential may take a long descending walk to evaluate. -/
theorem potential (down : Descends e) (join : Joins e) :
    ∃ value : Nat → Bool, ∀ {v b u}, e v b u → value v = (b ^^ value u) := by
  classical
  let value := fun v => Classical.choose (some_end (e := e) down v)
  have spec (v) : Ends e v (value v) := Classical.choose_spec (some_end (e := e) down v)
  refine ⟨value, ?_⟩
  intro v b u edge
  obtain ⟨t, walk, final⟩ := spec u
  exact unique_end (e := e) down join v _ _ (spec v) ⟨t, .more edge walk, final⟩

/-- A paused leg contributes zero to a paired derivation. -/
def Hop (e : Edge) (v : Nat) (a : Bool) (u : Nat) : Prop :=
  (u = v ∧ a = false) ∨ e v a u

private theorem prependHop (h : Hop e v a u) (tail : Walk e u b t) :
    Walk e v (a ^^ b) t := by
  rcases h with ⟨rfl, rfl⟩ | edge
  · simpa using tail
  · exact .more edge tail

abbrev Obligations := Nat → Nat → Bool → Prop

def Progress (e : Edge) (J : Obligations) : Prop :=
  ∀ v w c, J v w c → (v = w ∧ c = false) ∨
    ∃ u t a b, Hop e v a u ∧ Hop e w b t ∧ u + t < v + w ∧ J u t ((a ^^ b) ^^ c)

private theorem cancelPair (a b c i j : Bool) (eqn : (i ^^ j) = ((a ^^ b) ^^ c)) :
    ((a ^^ i) ^^ (b ^^ j)) = c := by
  cases a <;> cases b <;> cases c <;> cases i <;> cases j <;> simp_all

/-- A local progress relation provides concrete joining walks even without
    a circuit that computes a trajectory at a binary time index. -/
theorem progress_joins (h : Progress e J) (v w : Nat) (c : Bool) (start : J v w c) :
    ∃ z i j, Walk e v i z ∧ Walk e w j z ∧ (i ^^ j) = c := by
  generalize total : v + w = n
  induction n using Nat.strongRecOn generalizing v w c with
  | ind n ih =>
    rcases h v w c start with ⟨rfl, rfl⟩ | ⟨u, t, a, b, legh, regh, lower, next⟩
    · exact ⟨v, false, false, .stop _, .stop _, rfl⟩
    · obtain ⟨z, i, j, walkL, walkR, eqn⟩ := ih (u+t) (by omega) u t _ next rfl
      exact ⟨z, _, _, prependHop legh walkL, prependHop regh walkR, cancelPair _ _ _ _ _ eqn⟩

end DifferenceWitness
