import Std

namespace NativeOrderedDiagrams

def run (step : S → Bool → S) (s : S) : List Bool → S
  | [] => s
  | b :: bs => run step (step s b) bs

def productStep (left : S → Bool → S) (right : T → Bool → T)
    (p : S × T) (b : Bool) : S × T := (left p.1 b, right p.2 b)

theorem product_run (left : S → Bool → S) (right : T → Bool → T)
    (s : S) (t : T) (bits : List Bool) :
    run (productStep left right) (s,t) bits = (run left s bits, run right t bits) := by
  induction bits generalizing s t with
  | nil => rfl
  | cons b bs ih => exact ih (left s b) (right t b)

def translate (emit : U → Bool → Bool) (next : U → Bool → U)
    (u : U) : List Bool → List Bool
  | [] => []
  | b :: bs => emit u b :: translate emit next (next u b) bs

def translatedStep (step : S → Bool → S) (emit : U → Bool → Bool)
    (next : U → Bool → U) (p : U × S) (b : Bool) : U × S :=
  (next p.1 b, step p.2 (emit p.1 b))

theorem translated_run (step : S → Bool → S) (emit : U → Bool → Bool)
    (next : U → Bool → U) (s : S) (u : U) (bits : List Bool) :
    (run (translatedStep step emit next) (u,s) bits).2 =
      run step s (translate emit next u bits) := by
  induction bits generalizing s u with
  | nil => rfl
  | cons b bs ih => exact ih (step s (emit u b)) (next u b)

-- A state may include the layer number. Each layer's finite vector space
-- embeds in one ambient space by padding; restriction uses the layer in state
-- or one block of a direct sum for each layer.
theorem coordinates_follow (step : S → Bool → S) (lin : V → Bool → V)
    (coord : S → V) (edge : ∀ s b, coord (step s b) = lin (coord s) b)
    (s : S) (bits : List Bool) :
    coord (run step s bits) = run lin (coord s) bits := by
  induction bits generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [run]
    rw [ih (step s b), edge s b]

theorem additive_follow (restr : V → Bool → V) (plus : V → V → V)
    (linear : ∀ x y b, restr (plus x y) b = plus (restr x b) (restr y b))
    (x y : V) (bits : List Bool) :
    run restr (plus x y) bits = plus (run restr x bits) (run restr y bits) := by
  induction bits generalizing x y with
  | nil => rfl
  | cons b bs ih =>
    simp only [run]
    rw [linear, ih]

theorem xor_certificate (step : S → Bool → S) (restr : V → Bool → V)
    (plus : V → V → V) (coord : S → V) (out : S → Bool) (readout : V → Bool)
    (edge : ∀ s b, coord (step s b) = restr (coord s) b)
    (linear : ∀ x y b, restr (plus x y) b = plus (restr x b) (restr y b))
    (finish : ∀ x y, readout (plus x y) = Bool.xor (readout x) (readout y))
    (x y z : S) (bits : List Bool)
    (leaf : ∀ s ∈ [x,y,z], out (run step s bits) = readout (coord (run step s bits)))
    (root : coord z = plus (coord x) (coord y)) :
    out (run step z bits) = Bool.xor (out (run step x bits)) (out (run step y bits)) := by
  rw [leaf z (by simp), leaf x (by simp), leaf y (by simp),
      coordinates_follow step restr coord edge z bits, coordinates_follow step restr coord edge x bits,
      coordinates_follow step restr coord edge y bits, root, additive_follow restr plus linear, finish]

end NativeOrderedDiagrams
