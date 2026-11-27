import Std

namespace LocalProofCommitments

/-- `D` lower-bounds the size of each inconsistent list, allowing repetitions. -/
def ConflictFloor {X I : Type} (pass : X → I → Prop) (D : Nat) : Prop :=
  ∀ tests : List I, (∀ x, ∃ i ∈ tests, ¬ pass x i) → D ≤ tests.length

theorem flat_length_le {C I : Type} (colors : List C) (block : C → List I) (q : Nat)
    (bound : ∀ c ∈ colors, (block c).length ≤ q) :
    (colors.flatMap block).length ≤ colors.length * q := by
  induction colors with
  | nil => simp
  | cons c rest ih =>
    have hb := bound c (by simp)
    have hr := ih (by intro k hk; exact bound k (by simp [hk]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Taking the union of the per-color blockers rules out every assignment. -/
theorem all_color_blockers {X I C : Type} (pass : X → I → Prop) (D q : Nat)
    (floor : ConflictFloor pass D) (color : X → C) (colors : List C)
    (covers : ∀ x, color x ∈ colors) (block : C → List I)
    (bound : ∀ c ∈ colors, (block c).length ≤ q)
    (blocks : ∀ x, ∃ i ∈ block (color x), ¬ pass x i) : D ≤ colors.length * q := by
  apply Nat.le_trans (floor (colors.flatMap block) ?_) (flat_length_le colors block q bound)
  intro x
  obtain ⟨i, hi, hfail⟩ := blocks x
  exact ⟨i, List.mem_flatMap.mpr ⟨color x, covers x, hi⟩, hfail⟩

/-- Naming one block with a violated check realizes the matching upper bound. -/
theorem label_bad_block {X I C : Type} (pass : X → I → Prop) (block : C → List I)
    (conflict : ∀ x, ∃ c, ∃ i ∈ block c, ¬ pass x i) :
    ∃ color : X → C, ∀ c x, color x = c → ∃ i ∈ block c, ¬ pass x i := by
  classical
  refine ⟨fun x => Classical.choose (conflict x), ?_⟩
  intro c x hc
  subst c
  exact Classical.choose_spec (conflict x)

/-- A minimum parity conflict has odd total violation count on every proof. -/
def odd : List Bool → Bool
  | [] => false
  | a :: rest => a ^^ odd rest

theorem odd_has_violation (xs : List Bool) (h : odd xs = true) : true ∈ xs := by
  induction xs with
  | nil => simp [odd] at h
  | cons a as ih =>
    cases a with
    | true => simp
    | false =>
      have ht : odd as = true := by simpa [odd] using h
      simp [ih ht]

theorem parity_commitment_blocks {X : Type} (before : X → List Bool) (last : X → Bool)
    (conflict : ∀ x, (odd (before x) ^^ last x) = true) (commitment : List Bool) :
    (∀ x, before x = commitment → true ∈ before x) ∨
    (∀ x, before x = commitment → last x = true) := by
  cases hc : odd commitment with
  | true =>
    exact Or.inl (by intro x hx; rw [hx]; exact odd_has_violation commitment hc)
  | false =>
    apply Or.inr
    intro x hx
    simpa [hx, hc] using conflict x

def factorProduct : List Nat → Nat
  | [] => 1
  | b :: rest => b * factorProduct rest

def reachable {State : Type} (edge : Nat → State → State → Prop) :
    List Nat → State → State → Prop
  | [], s, last => s = last
  | b :: rest, s, last => ∃ next, edge b s next ∧ reachable edge rest next last

/-- On an adversarial transcript, `before ≤ factor * after` at each batch.
    Composing achievable replies multiplies the batch factors. -/
theorem batch_survivor {State : Type} (cost : State → Nat) (factors : List Nat)
    (canReply : Nat → State → State → Prop)
    (survives : ∀ b s, ∃ next, canReply b s next ∧ cost s ≤ b * cost next)
    (s : State) : ∃ last, reachable canReply factors s last ∧
        cost s ≤ factorProduct factors * cost last := by
  induction factors generalizing s with
  | nil => exact ⟨s, rfl, by simp [factorProduct]⟩
  | cons b rest ih =>
    obtain ⟨next, access, bound⟩ := survives b s
    obtain ⟨last, path, remaining⟩ := ih next
    refine ⟨last, ⟨next, access, path⟩, ?_⟩
    have total := Nat.le_trans bound (Nat.mul_le_mul_left b remaining)
    simpa [factorProduct, Nat.mul_assoc] using total

end LocalProofCommitments
