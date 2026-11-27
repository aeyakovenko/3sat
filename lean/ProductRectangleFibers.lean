import Std

namespace ProductRectangleFibers

section Graph

variable {X Y U V : Type} {f : X → Y → U × V}
variable {left : X → U → Prop} {right : Y → V → Prop}

/-- Any combination of the two local pairs must belong to the function graph. -/
def InsideGraph (f : X → Y → U × V) (left : X → U → Prop) (right : Y → V → Prop) :=
  ∀ x u y v, left x u → right y v → f x y = (u, v)

theorem unique_left_output (sound : InsideGraph f left right)
    {x u u' y v} (h : left x u) (h' : left x u') (opposite : right y v) : u = u' := by
  have eq := (sound x u y v h opposite).symm.trans (sound x u' y v h' opposite)
  exact congrArg Prod.fst eq

theorem unique_right_output (sound : InsideGraph f left right)
    {x u y v v'} (opposite : left x u) (h : right y v) (h' : right y v') : v = v' := by
  have eq := (sound x u y v opposite h).symm.trans (sound x u y v' opposite h')
  exact congrArg Prod.snd eq

end Graph

variable {I K J : Type}

/-- Matrix multiplication over the two-element field at one output position.
    The list enumerates the middle indices. No field library is assumed. -/
def dot : List K → (K → Bool) → (K → Bool) → Bool
  | [], _, _ => false
  | k :: rest, a, b => (a k && b k) ^^ dot rest a b

private theorem combine (a b c r s : Bool) :
    (((a ^^ b) && c) ^^ (r ^^ s)) = (((a && c) ^^ r) ^^ ((b && c) ^^ s)) := by
  cases a <;> cases b <;> cases c <;> cases r <;> cases s <;> rfl

theorem dot_xor (middle : List K) (a a' b : K → Bool) :
    dot middle (fun k => a k ^^ a' k) b = (dot middle a b ^^ dot middle a' b) := by
  induction middle with
  | nil => rfl
  | cons k ks ih =>
    simp only [dot, ih]
    exact combine _ _ _ _ _

def merge (leftMask : I → K → Bool) (a b : I → K → Bool) (i : I) (k : K) :=
  if leftMask i k then a i k else b i k

/-- Difference of two left fibers, filled with zero in all right positions. -/
def leftDifference (leftMask : I → K → Bool) (a a' : I → K → Bool) (i : I) (k : K) :=
  if leftMask i k then a i k ^^ a' i k else false

/-- At fixed B, varying the left A-block in a positive rectangle annihilates
    every right C coordinate. The two left output assignments can differ. -/
theorem left_difference_in_right_kernel
    (middle : List K) (b : K → J → Bool)
    (leftA : I → K → Bool) (rightC : I → J → Bool)
    (left right : (I → K → Bool) → (I → J → Bool) → Prop)
    (sound : ∀ a c ar cr, left a c → right ar cr → ∀ i j, rightC i j = true →
      dot middle (merge leftA a ar i) (fun k => b k j) = cr i j)
    {a a' c c' ar cr} (ha : left a c) (ha' : left a' c') (others : right ar cr)
    (i : I) (j : J) (pos : rightC i j = true) :
    dot middle (leftDifference leftA a a' i) (fun k => b k j) = false := by
  have diff : leftDifference leftA a a' i =
      fun k => merge leftA a ar i k ^^ merge leftA a' ar i k := by
    funext k
    cases hp : leftA i k <;> simp [leftDifference, merge, hp]
  rw [diff, dot_xor, sound a c ar cr ha others i j pos, sound a' c' ar cr ha' others i j pos]
  exact Bool.xor_self _

end ProductRectangleFibers
