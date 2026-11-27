import Std

/-! Private completions on negative-matching edges of the two-layer sheet family. -/
namespace SheetLiftMultiplicity

structure Endpoint where
  value : Bool
  positive : Bool
  anchor : Bool
  deriving DecidableEq

abbrev Edge := Endpoint × Endpoint

def accepts (e : Endpoint) (b y z : Bool) : Bool :=
  let x := e.value
  let guard := ((x == y) && (y == z)) ||
    (!e.anchor && ((!x && !y && z) || (x && !y && !z)))
  guard && (e.positive || y || z) && (!b || !y || !z)

def choices (e : Endpoint) (b : Bool) : Nat :=
  (accepts e b false false).toNat + (accepts e b false true).toNat +
  (accepts e b true false).toNat + (accepts e b true true).toNat

/-- The only intact centers in layer two have a positive self-port. -/
def live (e : Endpoint) (b : Bool) : Bool :=
  if e.anchor then e.value && e.positive && !b else !e.value || e.positive || !b

def free (e : Endpoint) (b : Bool) : Nat :=
  (!e.anchor && e.positive && !(e.value && b)).toNat

def viable (s : Edge) : Bool := live s.1 s.2.value && live s.2 s.1.value

def freeBits (s : Edge) := free s.1 s.2.value + free s.2 s.1.value
def roots (s : Edge) := s.1.anchor.toNat + s.2.anchor.toNat
def ones (s : Edge) := s.1.value.toNat + s.2.value.toNat
def posOnes (s : Edge) := s.1.positive.toNat + s.2.positive.toNat
def cut (s : Edge) := (s.1.value != s.2.value).toNat
def edgeChoices (s : Edge) := choices s.1 s.2.value * choices s.2 s.1.value

theorem local_weight (s : Edge) (h : viable s = true) :
    edgeChoices s = 2 ^ freeBits s ∧
    freeBits s + roots s + ones s = cut s + posOnes s := by
  rcases s with ⟨⟨x,p,i⟩,⟨y,q,j⟩⟩
  decide +revert

def total (f : Edge → Nat) (es : List Edge) : Nat := (es.map f).sum
def witnesses : List Edge → Nat
  | [] => 1
  | s :: es => edgeChoices s * witnesses es

theorem edge_product (es : List Edge) (h : ∀ s ∈ es, viable s = true) :
    witnesses es = 2 ^ total freeBits es ∧
    total freeBits es + total roots es + total ones es = total cut es + total posOnes es := by
  induction es with
  | nil => simp [witnesses, total]
  | cons s es ih =>
    obtain ⟨sw, sc⟩ := local_weight s (h s (by simp))
    obtain ⟨ew, ec⟩ := ih (fun e he => h e (by simp [he]))
    simp only [witnesses]
    simp only [total, List.map_cons, List.sum_cons] at ew ec ⊢
    constructor
    · rw [sw, ew, Nat.pow_add]
    · omega

/-- Positive partners permute all centers, so their total number of ones is
the center total. The negative matching is supplied as an actual list of pairs. -/
theorem exact_weight (es : List Edge) (h : ∀ s ∈ es, viable s = true)
    (permSum : total posOnes es = total ones es) (twoRoots : total roots es = 2) :
    2 ≤ total cut es ∧ witnesses es = 2 ^ (total cut es - 2) := by
  obtain ⟨hw, hc⟩ := edge_product es h
  have expEq : total freeBits es = total cut es - 2 := by omega
  exact ⟨by omega, hw.trans (congrArg (2 ^ ·) expEq)⟩

theorem antipodal_spent_pair (value : Bool) :
    edgeChoices (⟨value,!value,false⟩, ⟨!value,value,false⟩) = 2 := by
  decide +revert

#print axioms exact_weight
#print axioms antipodal_spent_pair

end SheetLiftMultiplicity
