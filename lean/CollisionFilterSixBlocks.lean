import Std

namespace CollisionFilterSixBlocks

/-- The five bits of one data-independent profile on ordered endpoints. -/
structure Profile where
  before : Bool
  leftEndpoint : Bool
  between : Bool
  rightEndpoint : Bool
  after : Bool

/-- Each diagram consists of the two equality classes specified below. -/
inductive Diagram where
  | a | b | c
deriving DecidableEq, Repr

/-- True denotes membership in the displayed first triple. -/
def firstTriple (d : Diagram) (v : Nat) : Bool :=
  match d with
  | .a => v == 0 || v == 2 || v == 3
  | .b => v == 0 || v == 2 || v == 4
  | .c => v == 0 || v == 1 || v == 4

/-- Exactly the genuine unordered equal pairs, once each, at vertices 0 to 5. -/
def equalPairs (d : Diagram) : List (Nat × Nat) :=
  (List.range 6).flatMap fun i =>
    (((List.range 6).filter fun j => i < j && firstTriple d i == firstTriple d j).map
      fun j => (i, j))

/-- All diagrams are honest partitions into two triangles, with six witnesses. -/
theorem diagram_counts (d : Diagram) :
    ((List.range 6).filter (firstTriple d)).length = 3 ∧
    ((List.range 6).filter (fun i => !(firstTriple d i))).length = 3 ∧
    (equalPairs d).length = 6 := by
  cases d <;> decide

/-- For i<j, these branches partition the six coordinates into the five regions. -/
def selected (p : Profile) (i j v : Nat) : Bool :=
  if v < i then p.before else
  if v = i then p.leftEndpoint else
  if v < j then p.between else
  if v = j then p.rightEndpoint else p.after

def edgeLabel (p : Profile) (i j : Nat) : BitVec 6 :=
  (List.range 6).foldl (fun word v =>
    if selected p i j v then word ||| ((1 : BitVec 6) <<< v) else word) 0

def syndrome (p : Profile) (d : Diagram) : BitVec 6 :=
  (equalPairs d).foldl (fun word e => word ^^^ edgeLabel p e.1 e.2) 0

def outerBit (p : Profile) := Bool.xor p.before p.after

def middleBit (p : Profile) :=
  Bool.xor p.leftEndpoint (Bool.xor p.between (Bool.xor p.rightEndpoint p.after))

def choose (p : Profile) : Diagram :=
  if outerBit p then (if middleBit p then .c else .a)
  else (if middleBit p then .b else .a)

set_option maxRecDepth 8192 in
/-- The only closed profile check is a 32-case kernel computation. Bits 2 and 3
are the common signal 12. Every parity is computed from actual equal pairs. -/
theorem chosen_value (p : Profile) :
    syndrome p (choose p) =
      (if outerBit p || middleBit p then (12 : BitVec 6) else 0) := by
  rcases p with ⟨a, b, c, d, e⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem one_plane (p : Profile) :
    syndrome p (choose p) = 0 ∨ syndrome p (choose p) = 12 := by
  rw [chosen_value]
  cases (outerBit p || middleBit p) <;> simp

/-- A nonempty even single-plane pattern can vanish, or two nonempty even
patterns from the two planes have the same six-bit value and cancel. -/
theorem two_planes (p q : Profile) :
    (∃ d, syndrome p d = 0) ∨ (∃ d, syndrome q d = 0) ∨
    (∃ d f, syndrome p d = syndrome q f ∧ syndrome p d ^^^ syndrome q f = 0) := by
  rcases one_plane p with hp | hp
  · exact Or.inl ⟨choose p, hp⟩
  rcases one_plane q with hq | hq
  · exact Or.inr (Or.inl ⟨choose q, hq⟩)
  · exact Or.inr (Or.inr ⟨choose p, choose q, hp.trans hq.symm, by rw [hp, hq]; decide⟩)

end CollisionFilterSixBlocks
