import Std

namespace BoundaryRelation

universe u

/-- Join two boundary conditions at the shared intermediate state. -/
def join {State : Type u} (P Q : State → State → Prop) (x z : State) : Prop :=
  ∃ y, P x y ∧ Q y z

/-- Exactly 2^l transitions, recursively bisected. -/
def dyadic {State : Type u} (step : State → State → Prop) : Nat → State → State → Prop
  | 0 => step
  | l + 1 => join (dyadic step l) (dyadic step l)

/-- Ordinary step-by-step paths, including a zero-step path. -/
def walk {State : Type u} (step : State → State → Prop) : Nat → State → State → Prop
  | 0 => fun x y => x = y
  | n+1 => join step (walk step n)

theorem split_walk {State : Type u} (step : State → State → Prop) (a b : Nat) :
    ∀ x z, walk step (a+b) x z ↔ join (walk step a) (walk step b) x z := by
  induction a with
  | zero => intro x z; simp [walk, join]
  | succ a ih =>
    intro x z
    rw [Nat.succ_add]
    constructor
    · rintro ⟨u, hxu, huz⟩
      obtain ⟨v, huv, hvz⟩ := (ih u z).mp huz
      exact ⟨v, ⟨u, hxu, huv⟩, hvz⟩
    · rintro ⟨v, ⟨u, hxu, huv⟩, hvz⟩
      exact ⟨u, hxu, (ih u z).mpr ⟨v, huv, hvz⟩⟩

theorem dyadic_walk {State : Type u} (step : State → State → Prop) (l : Nat) :
    ∀ x y, dyadic step l x y ↔ walk step (2^l) x y := by
  induction l with
  | zero => intro x y; simp [dyadic, walk, join]
  | succ l ih =>
    intro x z
    rw [Nat.pow_succ, Nat.mul_two, split_walk]
    constructor
    · rintro ⟨y, hxy, hyz⟩
      exact ⟨y, (ih x y).mp hxy, (ih y z).mp hyz⟩
    · rintro ⟨y, hxy, hyz⟩
      exact ⟨y, (ih x y).mpr hxy, (ih y z).mpr hyz⟩

theorem covered {State : Type u} (step : State → State → Prop)
    (R : Nat → State → State → Prop)
    (base : ∀ x y, step x y → R 0 x y)
    (close : ∀ l x y z, R l x y → R l y z → R (l+1) x z)
    (l : Nat) : ∀ x y, dyadic step l x y → R l x y := by
  induction l with
  | zero => exact base
  | succ l ih =>
    intro x z h
    obtain ⟨y, hxy, hyz⟩ := h
    exact close l x y z (ih x y hxy) (ih y z hyz)

theorem no_path {State : Type u} (step : State → State → Prop)
    (R : Nat → State → State → Prop) (start : State) (accept : State → Prop)
    (base : ∀ x y, step x y → R 0 x y)
    (close : ∀ l x y z, R l x y → R l y z → R (l+1) x z)
    (l : Nat) (separates : ∀ y, R l start y → ¬ accept y) :
    ¬ ∃ y, dyadic step l start y ∧ accept y := by
  rintro ⟨y, path, yes⟩
  exact separates y (covered step R base close l start y path) yes

/-- Local witness construction and merging give a sound existential upper bound. -/
theorem witness_no_path {State : Type u} {Choice : Type} (Proof : Nat → Type)
    (E : State → State → Choice → Prop) (C : (l : Nat) → State → State → Proof l → Prop)
    (seed : State → State → Choice → Proof 0)
    (merge : (l : Nat) → State → State → State → Proof l → Proof l → Proof (l+1))
    (base : ∀ x y e, E x y e → C 0 x y (seed x y e))
    (close : ∀ l x y z p q, C l x y p → C l y z q → C (l+1) x z (merge l x y z p q))
    (l : Nat) (start : State) (accept : State → Prop)
    (separates : ∀ y p, C l start y p → ¬accept y) :
    ¬ ∃ y, dyadic (fun x v => ∃ e, E x v e) l start y ∧ accept y := by
  apply no_path (fun x v => ∃ e, E x v e) (fun i x v => ∃ p, C i x v p) start accept
  · rintro x y ⟨e, he⟩
    exact ⟨seed x y e, base x y e he⟩
  · rintro i x y z ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨merge i x y z p q, close i x y z p q hp hq⟩
  · rintro y ⟨p, hp⟩
    exact separates y p hp

/-- Any accepted upper-bound certificate induces a separator on a midpoint family. -/
theorem midpoint {State : Type u} {Word : Type} (s : State) (mid : Word → State)
    (P Q : State → State → Prop) (accept : State → Prop) (A B : Word → Prop)
    (left : ∀ w, A w → P s (mid w))
    (right : ∀ w, B w → ∃ y, Q (mid w) y ∧ accept y)
    (safe : ∀ y, join P Q s y → ¬accept y) :
    (∀ w, A w → P s (mid w)) ∧ (∀ w, B w → ¬P s (mid w)) := by
  refine ⟨left, ?_⟩
  intro w hb hp
  obtain ⟨y, hq, ha⟩ := right w hb
  exact safe y ⟨mid w, hp, hq⟩ ha

#print axioms dyadic_walk
#print axioms covered
#print axioms no_path
#print axioms witness_no_path
#print axioms midpoint
end BoundaryRelation
