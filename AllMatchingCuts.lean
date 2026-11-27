import Std

/-! Local identities for indexing matching cuts and compiling clause selection. -/

namespace AllMatchingCuts

def drop (x y : Bool) := x && !y

def intact (x a b : Bool) := (x || a) && (!x || !b)

/-- The edge joins physical left value u₀ to the complemented right value v₁.
Its negative partners have physical values !u₁ and v₀. -/
theorem restored_anchors (u₀ u₁ v₀ v₁ : Bool) :
    (intact u₀ (!v₁) (!u₁) && intact (!v₁) u₀ v₀) =
      ((!v₀ || v₁) && (!v₁ || u₀) && (!u₀ || u₁)) := by decide +revert

theorem selected_anchors (u₀ u₁ v₀ v₁ : Bool) :
    (intact u₀ u₀ (!u₁) && intact (!v₁) (!v₁) v₀) = (u₀ && u₁ && !v₀ && !v₁) :=
  by decide +revert

/-- Four Boolean cycle edges carry only compatible signs at once. -/
theorem socket_signs (a b c d : Bool) :
    !((drop a b || drop c d) && (drop b c || drop d a)) = true := by decide +revert

/-- Every choice of sockets of one polarity is its exact descent set. -/
theorem realize_sockets (a b c d : Bool)
    (h : !((a || c) && (b || d)) = true) :
    drop a b = a ∧ drop b c = b ∧ drop c d = c ∧ drop d a = d := by decide +revert

theorem active_clause_has_literal (x y : Bool) :
    (drop true x || drop x y || drop y false) = true := by decide +revert

/-- A choice of one literal fixes the two remaining public bits on the active
clause gap. The first, second, third flags are in the order of its q-edges. -/
theorem choose_literal (a b c : Bool)
    (h : a.toNat + b.toNat + c.toNat = 1) :
    drop true (!a) = a ∧ drop (!a) c = b ∧ drop c false = c := by decide +revert

#print axioms restored_anchors
#print axioms choose_literal

end AllMatchingCuts
