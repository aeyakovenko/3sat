import Std

namespace SignRestriction

/-- The position of each sign is fixed. A true sign requests the positive literal. -/
def signedLiteral (sign value : Bool) : Bool := if sign then value else !value

theorem signedLiteral_true (s v : Bool) : signedLiteral s v = true ↔ v = s := by
  cases s <;> cases v <;> decide

/-- A verifier with auxiliary witness wires and one unit pin per input wire. -/
theorem satisfiable_with_pins {I W : Type} (verify : (I → Bool) → W → Prop)
    (input : I → Bool) :
    (∃ wire w, verify wire w ∧ ∀ i, signedLiteral (input i) (wire i) = true) ↔
      ∃ w, verify input w := by
  constructor
  · rintro ⟨wire, w, ok, pins⟩
    have same : wire = input := funext fun i => (signedLiteral_true _ _).mp (pins i)
    exact ⟨w, same ▸ ok⟩
  · rintro ⟨w, ok⟩
    exact ⟨input, w, ok, fun i => (signedLiteral_true _ _).mpr rfl⟩

/-- Nested tuples make coordinate order explicit in Shannon interpolation. -/
def Point (A : Type) : Nat → Type
  | 0 => Unit
  | n+1 => A × Point A n

/-- A face fixes some coordinates and consumes each free coordinate exactly once. -/
inductive Face : Nat → Nat → Type where
  | nil : Face 0 0
  | fixed (b : Bool) (rest : Face m n) : Face m (n+1)
  | free (complement : Bool) (rest : Face m n) : Face (m+1) (n+1)

def Face.apply {A : Type} (embed : Bool → A) (flip : A → A) :
    {m n : Nat} → Face m n → Point A m → Point A n
  | _, _, .nil, _ => ()
  | _, _, .fixed b rest, x => (embed b, rest.apply embed flip x)
  | _, _, .free c rest, x => (if c then flip x.1 else x.1, rest.apply embed flip x.2)

/-- Over a field take mix t a b = (1-t)*a + t*b. -/
def interpolate {K : Type} (mix : K → K → K → K) :
    {n : Nat} → (Point Bool n → K) → Point K n → K
  | 0, f, _ => f ()
  | n+1, f, x => mix x.1
      (interpolate mix (n := n) (fun tail => f (false, tail)) x.2)
      (interpolate mix (n := n) (fun tail => f (true, tail)) x.2)

/-- Coordinate restriction commutes with interpolation, including reversed signs.
    For field interpolation embed false = 0, embed true = 1 and flip t = 1-t. -/
theorem interpolate_face {K : Type} (mix : K → K → K → K) (embed : Bool → K)
    (flip : K → K) (atZero : ∀ a b, mix (embed false) a b = a)
    (atOne : ∀ a b, mix (embed true) a b = b)
    (swap : ∀ t a b, mix (flip t) a b = mix t b a)
    {m n : Nat} (face : Face m n) (f : Point Bool n → K) (x : Point K m) :
    interpolate mix (n := n) f (face.apply embed flip x) =
      interpolate mix (n := m) (fun y => f (face.apply id Bool.not y)) x := by
  induction face with
  | nil => rfl
  | fixed b rest ih =>
    cases b <;> simp only [Face.apply, interpolate, atZero, atOne, id_eq] <;> apply ih
  | free c rest ih =>
    cases c <;> simp only [Face.apply, interpolate, Bool.false_eq_true, if_false, if_true,
      Bool.not_false, Bool.not_true, swap, ih]

end SignRestriction
