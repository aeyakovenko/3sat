import Std

namespace HardSiblingTimeout

/-- One portfolio member, at one queried length, on the two children of a node.
    A missing verdict denotes a timeout. -/
structure Reply where
  left : Option Bool
  right : Option Bool

def firstAnswer (get : Reply → Option Bool) : List Reply → Option Bool
  | [] => none
  | r :: rs =>
    match get r with
    | some b => some b
    | none => firstAnswer get rs

theorem firstAnswer_none_iff (get : Reply → Option Bool) (rs : List Reply) :
    firstAnswer get rs = none ↔ ∀ r ∈ rs, get r = none := by
  induction rs with
  | nil => simp [firstAnswer]
  | cons r rs ih =>
    cases e : get r <;> simp [firstAnswer, e, ih]

theorem firstAnswer_sound (get : Reply → Option Bool) (rs : List Reply) (b : Bool)
    (sound : ∀ r ∈ rs, get r = none ∨ get r = some b) :
    firstAnswer get rs = none ∨ firstAnswer get rs = some b := by
  induction rs with
  | nil => simp [firstAnswer]
  | cons r rs ih =>
    rcases sound r (by simp) with h | h
    · simpa [firstAnswer, h] using ih (fun s hs => sound s (by simp [hs]))
    · simp [firstAnswer, h]

inductive Side where
  | left | right

/-- Prioritize a YES, then take the other child for a NO.
    In the absence of both reports, take the left child. -/
def choose : Option Bool → Option Bool → Side
  | some true, _ => .left
  | _, some true => .right
  | some false, _ => .right
  | _, some false => .left
  | none, none => .left

def sideValue (side : Side) (left right : Bool) : Bool :=
  match side with
  | .left => left
  | .right => right

private theorem lossAtChoice (left right : Bool) (l r : Option Bool)
    (hl : l = none ∨ l = some left) (hr : r = none ∨ r = some right)
    (parent : (left || right) = true)
    (loss : sideValue (choose l r) left right = false) :
    left ≠ right ∧ l = none ∧ r = none := by
  cases left <;> cases right <;> rcases hl with hl | hl <;> rcases hr with hr | hr <;>
    subst l <;> subst r <;> simp_all [choose, sideValue]

def chosenSide (rs : List Reply) : Side :=
  choose (firstAnswer Reply.left rs) (firstAnswer Reply.right rs)

def soundAt (rs : List Reply) (left right : Bool) : Prop :=
  (∀ r ∈ rs, r.left = none ∨ r.left = some left) ∧
  (∀ r ∈ rs, r.right = none ∨ r.right = some right)

def allTimedOut (rs : List Reply) : Prop :=
  ∀ r ∈ rs, r.left = none ∧ r.right = none

theorem lostFork (rs : List Reply) (left right : Bool)
    (sound : soundAt rs left right) (parent : (left || right) = true)
    (loss : sideValue (chosenSide rs) left right = false) :
    left ≠ right ∧ allTimedOut rs := by
  obtain ⟨hd, hl, hr⟩ := lossAtChoice left right _ _
    (firstAnswer_sound _ _ _ sound.1) (firstAnswer_sound _ _ _ sound.2) parent loss
  exact ⟨hd, fun r h => ⟨(firstAnswer_none_iff _ _).mp hl r h,
                         (firstAnswer_none_iff _ _).mp hr r h⟩⟩

/-- Leaves record the truth of complete assignments. Each internal node
    carries the entire finite list of paired replies obtained at that node. -/
inductive Tree where
  | leaf (value : Bool)
  | fork (replies : List Reply) (left right : Tree)

def sat : Tree → Bool
  | .leaf b => b
  | .fork _ l r => sat l || sat r

def outcome : Tree → Bool
  | .leaf b => b
  | .fork rs l r => sideValue (chosenSide rs) (outcome l) (outcome r)

def soundTree : Tree → Prop
  | .leaf _ => True
  | .fork rs l r => soundAt rs (sat l) (sat r) ∧ soundTree l ∧ soundTree r

/-- The hard fork lies on the actual path picked by the replies. -/
def visitedHardFork : Tree → Prop
  | .leaf _ => False
  | .fork rs l r => (sat l ≠ sat r ∧ allTimedOut rs) ∨
    match chosenSide rs with
    | .left => visitedHardFork l
    | .right => visitedHardFork r

theorem failed_search_has_visited_hard_fork (tree : Tree)
    (sound : soundTree tree) (possible : sat tree = true) (failed : outcome tree = false) :
    visitedHardFork tree := by
  induction tree with
  | leaf b => simp [sat] at possible; simp [outcome, possible] at failed
  | fork rs l r ihl ihr =>
    rcases sound with ⟨hs, hsl, hsr⟩
    cases h : chosenSide rs with
    | left =>
      by_cases hc : sat l = true
      · apply Or.inr
        simp only [h]
        exact ihl hsl hc (by simpa [outcome, h, sideValue] using failed)
      · apply Or.inl
        apply lostFork rs (sat l) (sat r) hs possible
        simp [h, sideValue, Bool.eq_false_iff.mpr hc]
    | right =>
      by_cases hc : sat r = true
      · apply Or.inr
        simp only [h]
        exact ihr hsr hc (by simpa [outcome, h, sideValue] using failed)
      · apply Or.inl
        apply lostFork rs (sat l) (sat r) hs possible
        simp [h, sideValue, Bool.eq_false_iff.mpr hc]

end HardSiblingTimeout
