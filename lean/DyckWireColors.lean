import Std

/-! Local identities underlying the binary straightening rule, and the
three-color separation of any two prescribed wires from a routing family
which cannot contain them simultaneously. -/
namespace DyckWireColors

def epsilon : Bool → Bool → Int
  | false, true => 1
  | true, false => -1
  | _, _ => 0

theorem uncross (a b c d : Bool) :
    epsilon a c * epsilon b d =
    epsilon a b * epsilon c d + epsilon a d * epsilon b c := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def indicator (a b : Bool) : Int := if a = b then 1 else 0

def wires (a b c x y z : Bool) : Int :=
  indicator a x * indicator b y * indicator c z

theorem alternating_three (a b c x y z : Bool) :
    wires a b c x y z + wires a b c y z x + wires a b c z x y =
    wires a b c x z y + wires a b c y x z + wires a b c z y x := by
  cases a <;> cases b <;> cases c <;> cases x <;> cases y <;> cases z <;> decide

inductive Color | first | second | rest deriving DecidableEq

def paint {α : Type} [DecidableEq α] (first second tested : α) : Color :=
  if tested = first then .first else if tested = second then .second else .rest

theorem agrees_with_private_colors {α β : Type} [DecidableEq α] [DecidableEq β]
    (pi : α → β) (injective : ∀ ⦃i j⦄, pi i = pi j → i = j) (a b i : α) :
    paint a b i = paint (pi a) (pi b) (pi i) := by
  by_cases ha : i = a
  · simp [ha, paint]
  · have hpa : pi i ≠ pi a := fun eq => ha (injective eq)
    by_cases hb : i = b
    · simp only [paint, if_neg ha, if_neg hpa, if_pos hb, if_pos (congrArg pi hb)]
    · have hpb : pi i ≠ pi b := fun eq => hb (injective eq)
      simp [paint, ha, hb, hpa, hpb]

theorem two_fixed_destinations {α β : Type} [DecidableEq α] [DecidableEq β]
    (a b : α) (u v : β) (different : a ≠ b) (rho : α → β)
    (agree : ∀ i, paint a b i = paint u v (rho i)) :
    rho a = u ∧ rho b = v := by
  constructor
  · have h := agree a
    by_cases hu : rho a = u
    · exact hu
    · have h' : Color.first = (if rho a = v then Color.second else Color.rest) := by
        simpa only [paint, if_pos rfl, if_neg hu] using h
      split at h' <;> contradiction
  · have h := agree b
    by_cases hv : rho b = v
    · exact hv
    · have h' : Color.second = (if rho b = u then Color.first else Color.rest) := by
        simpa only [paint, if_neg (Ne.symm different), if_pos rfl, if_neg hv] using h
      split at h' <;> contradiction

theorem three_colors_separate {α β : Type} [DecidableEq α] [DecidableEq β]
    (a b : α) (different : a ≠ b) (pi : α → β)
    (injective : ∀ ⦃i j⦄, pi i = pi j → i = j) (allowed : (α → β) → Prop)
    (incompatible : ∀ rho, allowed rho → ¬(rho a = pi a ∧ rho b = pi b)) :
    (∀ i, paint a b i = paint (pi a) (pi b) (pi i)) ∧
    ∀ rho, allowed rho → ¬(∀ i, paint a b i = paint (pi a) (pi b) (rho i)) := by
  constructor
  · exact agrees_with_private_colors pi injective a b
  · intro rho hr matchAll
    exact incompatible rho hr
      (two_fixed_destinations a b (pi a) (pi b) different rho matchAll)

end DyckWireColors
