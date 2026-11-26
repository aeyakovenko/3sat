import S3ColorEquations

/-! Products of positive permutations of a common set of letters, with a
shared final anchor. The exhaustive cases use the six permutations already
identified with their actions on three colors in S3ColorEquations. -/

namespace ThreePermutationProducts

open S3ColorEquations

private instance decideExistsFin {n : Nat} (p : Fin n → Prop) [DecidablePred p] :
    Decidable (∃ x, p x) :=
  decidable_of_iff (¬ ∀ x, ¬ p x) (by classical simp)

def word {α : Type} (label : α → Perm) : List α → Perm
  | [] => one
  | a :: rest => prod (label a) (word label rest)

def relative (base other : Perm) : Perm := prod other (inv base)

private theorem identity_left : ∀ g, prod one g = g := by decide

/-- Outside a selected subalphabet all labels are the identity. -/
theorem project_word {α β : Type} (project : α → Option β) (label : β → Perm)
    (w : List α) :
    word (fun x => (project x).elim one label) w = word label (w.filterMap project) := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    simp only [word, ih]
    cases hx : project x <;> simp [List.filterMap, hx, word, identity_left]

/-- Two pairwise order tests suffice to distinguish three distinct comparison
functions. Each test mentions just two letters when its argument is a pair. -/
theorem two_tests {I : Type} (a b c : I → Bool)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    ∃ i j, (a i, a j) ≠ (b i, b j) ∧ (a i, a j) ≠ (c i, c j) ∧
      (b i, b j) ≠ (c i, c j) := by
  classical
  have different (f g : I → Bool) (hne : f ≠ g) : ∃ x, f x ≠ g x := by
    apply Classical.byContradiction
    intro h
    exact hne (funext (fun x => Classical.byContradiction (fun hx => h ⟨x, hx⟩)))
  obtain ⟨i, hi⟩ := different a b ab
  by_cases h : a i = c i
  · obtain ⟨j, hj⟩ := different a c ac
    exact ⟨i, j, fun e => hi (congrArg Prod.fst e), fun e => hj (congrArg Prod.snd e),
      fun e => hi (h.trans (congrArg Prod.fst e).symm)⟩
  · obtain ⟨j, hj⟩ := different b c bc
    exact ⟨i, j, fun e => hi (congrArg Prod.fst e), fun e => h (congrArg Prod.fst e),
      fun e => hj (congrArg Prod.snd e)⟩

/-- Enumerate orders by inserting each new letter at its mixed-radix digit. -/
def order : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, code =>
    let tail := order n (code / (n+1))
    tail.take (code % (n+1)) ++ [n] ++ tail.drop (code % (n+1))

/-- Every list in the small library is a permutation of the appropriate
alphabet, and its size is the factorial count. -/
theorem orders_checked :
    ([3,4] : List Nat).all (fun n =>
      let rows := (List.range (if n = 3 then 6 else 24)).map (order n)
      decide rows.Nodup && rows.all (fun w => decide (w.Perm (List.range n)))) = true := by
  decide

/-- The digits of a base-six counter provide arbitrary labels to four letters. -/
def digits (code : Fin 1296) (i : Nat) : Perm :=
  ⟨code.val / 6^i % 6, Nat.mod_lt _ (by decide)⟩

private def result (n : Nat) (p q : Fin 24) (a : Fin 1296) : Perm × Perm :=
  let base := word (digits a) (List.range n)
  (relative base (word (digits a) (order n p.val)),
   relative base (word (digits a) (order n q.val)))

/-- On three and four letters, every pair of rotation targets is attained by
each triple of distinct orders, after renaming the first order to 0,1,... . -/
theorem restricted_exhaustion (n : Nat) (hn : n = 3 ∨ n = 4)
    (p q : Fin 24) (hp : order n p.val ≠ List.range n)
    (hq : order n q.val ≠ List.range n) (hpq : order n p.val ≠ order n q.val)
    (u v : Color) : ∃ a : Fin 1296, result n p q a = (pack u false, pack v false) := by
  have census : ∀ t : Fin 2, ∀ i j : Fin 24,
      let n := 3 + t.val
      order n i.val ≠ List.range n → order n j.val ≠ List.range n →
      order n i.val ≠ order n j.val → ∀ u v : Color, ∃ a : Fin 1296,
      result n i j a = (pack u false, pack v false) := by native_decide
  rcases hn with rfl | rfl
  · exact census 0 p q hp hq hpq u v
  · exact census 1 p q hp hq hpq u v

private theorem rotation_of_relative : ∀ a b, reflected a = reflected b →
  pack (shift (relative a b)) false = relative a b := by decide

private theorem anchor_fixes : ∀ base goal, prod base (prod (inv base) goal) = goal := by decide

private theorem anchor_agrees : ∀ a b g h, relative a b = relative g h →
  prod b (prod (inv a) g) = h := by decide

/-- The finite census lifts to words of arbitrary length. The projection keeps
the distinguishing letters and renames them in the first word's order. -/
theorem realize_from_projection {α : Type} (words₀ words₁ words₂ : List α)
    (choose : α → Option Nat) (n : Nat) (hn : n = 3 ∨ n = 4) (p q : Fin 24)
    (r₀ : words₀.filterMap choose = List.range n)
    (r₁ : words₁.filterMap choose = order n p.val)
    (r₂ : words₂.filterMap choose = order n q.val)
    (hp : order n p.val ≠ List.range n) (hq : order n q.val ≠ List.range n)
    (hpq : order n p.val ≠ order n q.val)
    (g₀ g₁ g₂ : Perm)
    (h₁ : reflected g₀ = reflected g₁) (h₂ : reflected g₀ = reflected g₂) :
    ∃ (label : α → Perm) (anchor : Perm), prod (word label words₀) anchor = g₀ ∧
      prod (word label words₁) anchor = g₁ ∧ prod (word label words₂) anchor = g₂ := by
  obtain ⟨a, found⟩ := restricted_exhaustion n hn p q hp hq hpq
    (shift (relative g₀ g₁)) (shift (relative g₀ g₂))
  let label := fun x => (choose x).elim one (digits a)
  have e₀ : word label words₀ = word (digits a) (List.range n) := by
    rw [← r₀]; exact project_word _ _ _
  have e₁ : word label words₁ = word (digits a) (order n p.val) := by
    rw [← r₁]; exact project_word _ _ _
  have e₂ : word label words₂ = word (digits a) (order n q.val) := by
    rw [← r₂]; exact project_word _ _ _
  refine ⟨label, prod (inv (word label words₀)) g₀, anchor_fixes _ _, ?_, ?_⟩
  · apply anchor_agrees
    rw [e₀, e₁]
    exact (congrArg Prod.fst found).trans (rotation_of_relative _ _ h₁)
  · apply anchor_agrees
    rw [e₀, e₂]
    exact (congrArg Prod.snd found).trans (rotation_of_relative _ _ h₂)

/-- The three non-base modes compared with ABC. -/
def fourSignals (a b c : Perm) : Perm × Perm × Perm :=
  let base := prod a (prod b c)
  (relative base (prod a (prod c b)), relative base (prod b (prod c a)),
   relative base (prod c (prod b a)))

/-- Exactly 15 of the 27 triples of rotations occur. Here u=0 iff v=w. -/
theorem four_mode_iff : ∀ u v w : Color,
    (∃ a b c : Perm, fourSignals a b c = (pack u false, pack v false, pack w false)) ↔
    (u = 0 ↔ v = w) := by decide

end ThreePermutationProducts
