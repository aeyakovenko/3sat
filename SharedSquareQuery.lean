import Std

namespace SharedSquareQuery

def intact (x a b : Bool) := (x || a) && !(x && b)
def regular (x a b : Bool) := (!x || a || !b)

/-- The first and second switches replace the positive partners of c and a by themselves. -/
def pin (a b left right : Bool) :=
  intact a (if left then a else !b) (!a) &&
  intact (!b) (if right then !b else a) b &&
  regular (!a) b a && regular b (!a) (!b)

theorem pin_exact (a b left right : Bool) :
    pin a b left right = true ↔
      (b = true → a = true) ∧ (left = true → a = true) ∧ (right = true → b = false) := by
  decide +revert

theorem same_name (x left right : Bool) :
    pin x x left right = true ↔ (left = true → x = true) ∧ (right = true → x = false) := by
  decide +revert

theorem full_source (x cut : Bool) :
    (∃ b, pin x b cut cut = true) ↔ (cut = true → x = true) := by decide +revert

theorem full_sink (x cut : Bool) :
    (∃ a, pin a x cut cut = true) ↔ (cut = true → x = false) := by decide +revert

def box (c a b z : Bool) :=
  regular c a b && regular a c z && regular b z c && regular z b a

theorem implication (x y w : Bool) :
    box x (!w) (!y) w = true ↔ x = true → y = true := by decide +revert

inductive Walk {V : Type} (E : V → V → Prop) : V → V → Prop where
  | refl (v) : Walk E v v
  | step {s u v} : Walk E s u → E u v → Walk E s v

/-- All simultaneous positive and negative edits, including empty query sets. -/
theorem all_queries {V : Type} (E : V → V → Prop) (P N : V → Prop) :
    (∃ x : V → Prop, (∀ u v, E u v → x u → x v) ∧
                  (∀ s, P s → x s) ∧ (∀ t, N t → ¬ x t)) ↔
      (∀ s t, P s → N t → ¬ Walk E s t) := by
  constructor
  · rintro ⟨x, closed, pos, neg⟩ s t hp hn path
    apply neg t hn
    clear hn
    induction path with
    | refl => exact pos s hp
    | step prev edge ih => exact closed _ _ edge ih
  · intro h
    refine ⟨fun v => ∃ s, P s ∧ Walk E s v, ?_, ?_, ?_⟩
    · rintro u v edge ⟨s, hp, path⟩
      exact ⟨s, hp, .step path edge⟩
    · intro s hp
      exact ⟨s, hp, .refl s⟩
    · rintro t hn ⟨s, hp, path⟩
      exact h s t hp hn path

#print axioms all_queries
end SharedSquareQuery
