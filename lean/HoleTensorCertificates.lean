import Std

namespace HoleTensorCertificates

abbrev Row := Bool × Bool

def zero : Row := (false, false)
def add (u v : Row) : Row := (u.1 ^^ v.1, u.2 ^^ v.2)

/-- Membership in the binary linear span, expressed by closed subsets. -/
def Spanned (S : Row → Prop) (x : Row) : Prop :=
  ∀ P : Row → Prop, P zero →
    (∀ u v, P u → P v → P (add u v)) → (∀ u, S u → P u) → P x

def Covers (S : Row → Prop) : Prop := ∀ x, Spanned S x

/-- This is a binary node's outgoing row before linear combinations. -/
def joined (f : Row → Row → Row) (S T : Row → Prop) (x : Row) : Prop :=
  ∃ a b, S a ∧ T b ∧ x = f a b

/-- Full row spans at the two children and full local row span at their parent
give full contracted row span. This is the inductive argument for binary trees. -/
theorem full_at_parent (S T : Row → Prop) (f : Row → Row → Row)
    (fl0 : ∀ b, f zero b = zero) (fr0 : ∀ a, f a zero = zero)
    (fl : ∀ a b y, f (add a b) y = add (f a y) (f b y))
    (fr : ∀ x a b, f x (add a b) = add (f x a) (f x b))
    (left : Covers S) (right : Covers T)
    (port : Covers (fun z => ∃ a b, z = f a b)) : Covers (joined f S T) := by
  intro x P hz hp hin
  apply port x P hz hp
  rintro _ ⟨a,b,rfl⟩
  apply left a (fun a' => P (f a' b))
  · simpa only [fl0] using hz
  · intro i j hi hj
    simpa only [fl] using hp _ _ hi hj
  · intro a' ha
    apply right b (fun b' => P (f a' b'))
    · simpa only [fr0] using hz
    · intro i j hi hj
      simpa only [fr] using hp _ _ hi hj
    · intro b' hb
      exact hin _ ⟨a',b',ha,hb,rfl⟩

structure Matrix where
  a : Bool
  b : Bool
  c : Bool
  d : Bool

def mul (u v : Matrix) : Matrix :=
  ⟨(u.a && v.a) ^^ (u.b && v.c), (u.a && v.b) ^^ (u.b && v.d),
   (u.c && v.a) ^^ (u.d && v.c), (u.c && v.b) ^^ (u.d && v.d)⟩

def det (u : Matrix) := (u.a && u.d) ^^ (u.b && u.c)

theorem det_mul (u v : Matrix) : det (mul u v) = (det u && det v) := by
  rcases u with ⟨a,b,c,d⟩
  rcases v with ⟨p,q,r,s⟩
  revert a b c d p q r s
  decide

def identity : Matrix := ⟨true, false, false, true⟩

theorem det_path (factors : List Matrix) :
    det (factors.foldr mul identity) = factors.all det := by
  induction factors with
  | nil => rfl
  | cons u tail ih => simp only [List.foldr_cons, det_mul, List.all_cons, ih]

def bitParity (bits : List Bool) := bits.foldr (· ^^ ·) false

def travel (start : Bool) (bits : List Bool) := bits.foldl (· ^^ ·) start

theorem travel_eq (x : Bool) (bits : List Bool) :
    travel x bits = (x ^^ bitParity bits) := by
  induction bits generalizing x with
  | nil => simp [travel, bitParity]
  | cons b bs ih =>
    change travel (x ^^ b) bs = (x ^^ (b ^^ bitParity bs))
    rw [ih, Bool.xor_assoc]

/-- Closing factor admits (0,0), (0,1), and (1,1).
The two possible initial bits index all satisfying paths in the ring. -/
def closes (last first : Bool) := !last || first

theorem ring_count (bits : List Bool) :
    ([false, true].countP (fun first => closes (travel first bits) first)) =
      (if bitParity bits then 1 else 2) := by
  simp only [travel_eq]
  cases h : bitParity bits <;> rfl

end HoleTensorCertificates
