import Std

namespace ProjectedResolutionStep

abbrev Clause (L : Type) := L → Prop

def Sub {L : Type} (A B : Clause L) := ∀ x, A x → B x

def Join {L : Type} (A B : Clause L) (x : L) := A x ∨ B x

def WithLit {L : Type} (A : Clause L) (p x : L) := A x ∨ x = p

def Resolve {L : Type} (D E : Clause L) (p q x : L) :=
  (D x ∧ x ≠ p) ∨ (E x ∧ x ≠ q)

/-- p and q represent opposite signed images of the original pivot.
    When the projected conclusion is non-tautological, a skipped parent
    can only have been made tautological by the pivot and its complement.
    A stored line is a subclause of the corresponding projected parent. -/
theorem nonconstant_pivot {L : Type} (A B : Clause L) (p q : L)
    (compatible : ¬ (Join A B p ∧ Join A B q))
    (fromLeft fromRight : Clause L → Prop)
    (left : ¬ A q → ∃ D, fromLeft D ∧ Sub D (WithLit A p))
    (right : ¬ B p → ∃ E, fromRight E ∧ Sub E (WithLit B q)) :
    (∃ D, fromLeft D ∧ Sub D (Join A B)) ∨
    (∃ E, fromRight E ∧ Sub E (Join A B)) ∨
    (∃ D E, fromLeft D ∧ fromRight E ∧ D p ∧ E q ∧
       Sub (Resolve D E p q) (Join A B)) := by
  classical
  by_cases aq : A q
  · have bp : ¬ B p := fun h => compatible ⟨Or.inr h, Or.inl aq⟩
    obtain ⟨E, he, sub⟩ := right bp
    refine Or.inr (Or.inl ⟨E, he, ?_⟩)
    intro x hx
    rcases sub x hx with bx | rfl
    · exact Or.inr bx
    · exact Or.inl aq
  obtain ⟨D, hd, dsub⟩ := left aq
  by_cases bp : B p
  · refine Or.inl ⟨D, hd, ?_⟩
    intro x hx
    rcases dsub x hx with ax | rfl
    · exact Or.inl ax
    · exact Or.inr bp
  obtain ⟨E, he, esub⟩ := right bp
  by_cases dp : D p
  · by_cases eq : E q
    · refine Or.inr (Or.inr ⟨D,E,hd,he,dp,eq,?_⟩)
      intro x hx
      rcases hx with ⟨dx,hx⟩ | ⟨ex,hx⟩
      · exact Or.inl ((dsub x dx).resolve_right hx)
      · exact Or.inr ((esub x ex).resolve_right hx)
    · refine Or.inr (Or.inl ⟨E, he, ?_⟩)
      intro x ex
      rcases esub x ex with bx | rfl
      · exact Or.inr bx
      · exact (eq ex).elim
  · refine Or.inl ⟨D, hd, ?_⟩
    intro x dx
    rcases dsub x dx with ax | rfl
    · exact Or.inl ax
    · exact (dp dx).elim

/-- For a constant pivot, the parent where that pivot literal evaluates
    to false supplies a subclause without a resolution step. -/
theorem constant_pivot {L : Type} (A B E : Clause L) (s : Sub E B) :
    Sub E (Join A B) := fun x hx => Or.inr (s x hx)

theorem weakening {L : Type} (D A B : Clause L) (da : Sub D A) (ab : Sub A B) :
    Sub D B := fun x hx => ab x (da x hx)

end ProjectedResolutionStep
