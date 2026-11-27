import Std

namespace FirstReadReplay

/-- A local deterministic replay may request an incoming word adaptively. -/
inductive Reads (A W R : Type) where
  | done (out : R)
  | ask (address : A) (next : W → Reads A W R)

def result (mem : A → W) : Reads A W R → R
  | .done out => out
  | .ask a next => result mem (next (mem a))

def queried (mem : A → W) (target : A) : Reads A W R → Prop
  | .done _ => False
  | .ask a next => a = target ∨ queried mem target (next (mem a))

theorem agree_on_path (t : Reads A W R) (m₁ m₂ : A → W)
    (h : ∀ a, queried m₁ a t → m₁ a = m₂ a) : result m₁ t = result m₂ t := by
  induction t with
  | done => rfl
  | ask a next ih =>
    have ha := h a (Or.inl rfl)
    change result m₁ (next (m₁ a)) = result m₂ (next (m₂ a))
    rw [← ha]
    exact ih (m₁ a) (fun b hb => h b (Or.inr hb))

def possible (allowed : A → W → Prop) (t : Reads A W R) (a : A) : Prop :=
  ∃ mem : A → W, (∀ b, allowed b (mem b)) ∧ queried mem a t

/-- Admissibility of the actual memory need only hold at potentially queried addresses. -/
theorem fill_for_actual (allowed : A → W → Prop) (t : Reads A W R)
    (base actual : A → W) (hb : ∀ a, allowed a (base a))
    (ha : ∀ a, possible allowed t a → allowed a (actual a)) :
    ∃ mem : A → W, (∀ a, allowed a (mem a)) ∧ result mem t = result actual t := by
  classical
  let mem := fun a => if possible allowed t a then actual a else base a
  have good : ∀ a, allowed a (mem a) := by
    intro a
    by_cases hp : possible allowed t a
    · simpa [mem, hp] using ha a hp
    · simpa [mem, hp] using hb a
  refine ⟨mem, good, agree_on_path t mem actual ?_⟩
  intro a hq
  have hp : possible allowed t a := ⟨mem, good, hq⟩
  simp [mem, hp]

theorem stable_actual (allowed : A → W → Prop) (t : Reads A W R)
    (base actual : A → W) (hb : ∀ a, allowed a (base a))
    (ha : ∀ a, possible allowed t a → allowed a (actual a))
    (stable : ∀ mem, (∀ a, allowed a (mem a)) → result mem t = result base t) :
    result actual t = result base t := by
  obtain ⟨mem, hm, he⟩ := fill_for_actual allowed t base actual hb ha
  exact he.symm.trans (stable mem hm)

end FirstReadReplay
