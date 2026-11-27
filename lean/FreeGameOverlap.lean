import Std

namespace FreeGameOverlap

variable {Seed Address LeftQuestion RightQuestion Value : Type}

structure Game (Seed Address LeftQuestion RightQuestion Value : Type) where
  leftBlock : Seed → LeftQuestion
  rightBlock : Seed → RightQuestion
  queries : Seed → Address → Prop
  accepts : (s : Seed) → ({a // queries s a} → Value) → Prop

abbrev LeftStrategy (Seed Address LeftQuestion Value : Type) :=
  LeftQuestion → Seed → Address → Value

abbrev RightStrategy (Address RightQuestion Value : Type) :=
  RightQuestion → Address → Value

variable (g : Game Seed Address LeftQuestion RightQuestion Value)
variable (left : LeftStrategy Seed Address LeftQuestion Value)
variable (right : RightStrategy Address RightQuestion Value)

/-- Each left test has its own local assignment, while the right block
    supplies exactly one answer per address shared with that block. -/
def passes (i : LeftQuestion) (j : RightQuestion) : Prop :=
  (∀ s, g.leftBlock s = i → g.accepts s (fun a => left i s a.val)) ∧
  (∀ s t a, g.leftBlock s = i → g.rightBlock t = j → g.queries s a → g.queries t a →
    left i s a = right j a)

/-- If two occurrences disagree, using the SAME right strategy and question
    against both left blocks forces a rejection in at least one test. -/
theorem disagreement (s t : Seed) (a : Address) (qs : g.queries s a) (qt : g.queries t a)
    (different : left (g.leftBlock s) s a ≠ left (g.leftBlock t) t a) :
    ¬ passes g left right (g.leftBlock s) (g.rightBlock s) ∨
    ¬ passes g left right (g.leftBlock t) (g.rightBlock s) := by
  by_cases first : passes g left right (g.leftBlock s) (g.rightBlock s)
  · right
    intro second
    exact different ((first.2 s s a rfl rfl qs qs).trans
      (second.2 t s a rfl rfl qt qs).symm)
  · exact Or.inl first

/-- Perfect independent strategies yield a single PCP proof table. No
    right answer is allowed to depend on the left question. -/
theorem perfect_iff [Inhabited Value] :
    (∃ L R, ∀ i j, passes g L R i j) ↔
    ∃ proof : Address → Value, ∀ s, g.accepts s (fun a => proof a.val) := by
  classical
  constructor
  · rintro ⟨L, R, all⟩
    let proof := fun a : Address =>
      if h : ∃ s, g.queries s a then R (g.rightBlock (Classical.choose h)) a else default
    refine ⟨proof, ?_⟩
    intro s
    have equal : (fun a : {a // g.queries s a} => L (g.leftBlock s) s a.val) =
        fun a => proof a.val := by
      funext a
      have seen : ∃ u, g.queries u a.val := ⟨s, a.property⟩
      simp only [proof, dif_pos seen]
      exact (all (g.leftBlock s) (g.rightBlock (Classical.choose seen))).2
        s (Classical.choose seen) a.val rfl rfl a.property (Classical.choose_spec seen)
    rw [← equal]
    exact (all (g.leftBlock s) (g.rightBlock s)).1 s rfl
  · rintro ⟨proof, valid⟩
    exact ⟨fun _ _ a => proof a, fun _ a => proof a,
      fun _ _ => ⟨fun s _ => valid s, fun _ _ _ _ _ _ _ => rfl⟩⟩

/-- Sum over any finite weighted coupling, on a common integral mass scale.
    Repetition of sample points and zero weights are allowed. -/
noncomputable def mass {E : Type} (p : E → Prop) : List (E × Nat) → Nat := by
  classical
  exact List.foldr (fun w total => (if p w.1 then w.2 else 0) + total) 0

theorem mass_of_cover {E : Type} (d p q : E → Prop)
    (cover : ∀ e, d e → p e ∨ q e) (samples : List (E × Nat)) :
    mass d samples ≤ mass p samples + mass q samples := by
  classical
  induction samples with
  | nil => simp [mass]
  | cons x xs ih =>
    obtain ⟨e, w⟩ := x
    have pointwise : (if d e then w else 0) ≤
        (if p e then w else 0) + (if q e then w else 0) := by
      by_cases hd : d e
      · rcases cover e hd with hp | hq <;> simp_all
      · simp [hd]
    simp only [mass, List.foldr_cons] at ih ⊢
    exact Nat.le_trans (Nat.add_le_add pointwise ih) (by omega)

/-- Rational probabilities can be cleared to a shared denominator. The two
    error terms charge the two separate panel distributions. -/
theorem rejection_bound (δ d D p tv₀ tv₁ ℓ : Nat)
    (rounding : δ ≤ d + ℓ * D) (localTest : d ≤ p)
    (coupled : D ≤ 2*p + tv₀ + tv₁) :
    δ ≤ (1 + 2*ℓ)*p + ℓ*(tv₀ + tv₁) := by
  have total := Nat.le_trans rounding (Nat.add_le_add localTest (Nat.mul_le_mul_left ℓ coupled))
  simpa only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm ℓ 2,
    Nat.add_assoc] using total

end FreeGameOverlap
