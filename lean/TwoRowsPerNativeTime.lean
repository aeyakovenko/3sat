import Std

namespace TwoRowsPerNativeTime

def majority (x y z : Bool) : Bool := (x && y) || (x && z) || (y && z)

theorem literalMaj : ∀ p x y z : Bool,
    xor p (majority x y z) = majority (xor p x) (xor p y) (xor p z) := by decide

theorem clauseMaj : ∀ x₁ x₂ y₁ y₂ z₁ z₂ : Bool,
    (x₁ || x₂) = true → (y₁ || y₂) = true → (z₁ || z₂) = true →
    (majority x₁ y₁ z₁ || majority x₂ y₂ z₂) = true := by decide

variable {Var : Type}

abbrev Lit (Var : Type) := Var × Bool
abbrev Clause (Var : Type) := Lit Var × Lit Var

def lit (x : Var → Bool) (u : Lit Var) : Bool := xor u.2 (x u.1)

def satisfies (formula : Clause Var → Prop) (x : Var → Bool) : Prop :=
  ∀ c, formula c → (lit x c.1 || lit x c.2) = true

theorem modelsMaj {formula : Clause Var → Prop} {x y z : Var → Bool}
    (hx : satisfies formula x) (hy : satisfies formula y) (hz : satisfies formula z) :
    satisfies formula (fun k => majority (x k) (y k) (z k)) := by
  intro c hc
  simp only [lit, literalMaj]
  exact clauseMaj _ _ _ _ _ _ (hx c hc) (hy c hc) (hz c hc)

/-- Existentially projecting arbitrary auxiliary variables preserves the closure
    that excludes a single local AND switch. No finiteness hypothesis is needed. -/
theorem noProjectedAnd (formula : Clause Var → Prop) (u v g : Var) :
    ¬ ∀ a b c : Bool, (a && b) = c ↔ ∃ x : Var → Bool,
      satisfies formula x ∧ x u = a ∧ x v = b ∧ x g = c := by
  intro project
  obtain ⟨x, hx, hxu, hxv, hxg⟩ := (project false true false).mp rfl
  obtain ⟨y, hy, hyu, hyv, hyg⟩ := (project true false false).mp rfl
  obtain ⟨z, hz, hzu, hzv, hzg⟩ := (project true true true).mp rfl
  have bad := (project true true false).mpr ⟨_, modelsMaj hx hy hz,
    by simp [hxu, hyu, hzu, majority], by simp [hxv, hyv, hzv, majority],
    by simp [hxg, hyg, hzg, majority]⟩
  contradiction

end TwoRowsPerNativeTime
