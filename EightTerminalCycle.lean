import NestedClauseCycle

/-! Eight-terminal monotone 3-CNF. An assignment is an eight-bit terminal
word. In every split, each rectangle can use arbitrary predicates of its
own terminal bits. Its membership predicates need not be computable. -/
namespace EightTerminalCycle

abbrev Word := BitVec 8
abbrev Cut := Fin 256

/-- Each hexadecimal-free mask names one positive clause. -/
def verdict (x : Word) : Bool :=
  (x &&& 7 != 0) && (x &&& 11 != 0) && (x &&& 28 != 0) &&
  (x &&& 49 != 0) && (x &&& 100 != 0) && (x &&& 161 != 0)

def cutWord (m : Cut) : Word := BitVec.ofNat 8 m.val

def row (m x : Word) : Word := x &&& m
def col (m x : Word) : Word := x &&& ~~~m
def mix (m x y : Word) : Word := row m x ||| col m y

theorem mix_projections (m x y : Word) :
    row m (mix m x y) = row m x ∧ col m (mix m x y) = col m y := by
  constructor <;> ext i hi <;>
    simp only [row, col, mix, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not] <;>
    cases m[i] <;> simp

def terminals (m : Cut) : Nat := NestedClauseCycle.below m.val 8

def pick3 (i : Fin 3) (a b c : Word) : Word :=
  if i = 0 then a else if i = 1 then b else c

def pick5 (i : Fin 5) (a b c d e : Word) : Word :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else e

/-- Full assignments for the three certified diagonal ones. -/
def pairWitness (m : Cut) (i : Fin 3) : Word :=
  match m.val with
  | 3 => pick3 i 44 5 38
  | 5 => pick3 i 42 41 38
  | 6 => pick3 i 41 42 5
  | 9 => pick3 i 38 5 42
  | 10 => pick3 i 5 38 41
  | 12 => pick3 i 49 5 41
  | 17 => pick3 i 38 5 50
  | 18 => pick3 i 5 38 49
  | 20 => pick3 i 41 5 49
  | 24 | 136 => pick3 i 5 41 150
  | 33 => pick3 i 150 5 38
  | 34 => pick3 i 5 150 41
  | 36 => pick3 i 73 5 41
  | 40 => pick3 i 5 73 38
  | 48 => pick3 i 5 81 38
  | 65 => pick3 i 38 5 210
  | 66 | 96 => pick3 i 5 38 73
  | 68 => pick3 i 41 5 73
  | 72 => pick3 i 5 41 81
  | 80 => pick3 i 5 49 73
  | 129 => pick3 i 38 5 150
  | 130 => pick3 i 5 38 156
  | 132 => pick3 i 41 5 210
  | 144 => pick3 i 5 49 150
  | 160 => pick3 i 5 38 150
  | 192 => pick3 i 5 73 150
  | _ => 0

/-- Full assignments for the five certified diagonal ones. -/
def tripleWitness (m : Cut) (i : Fin 5) : Word :=
  match m.val with
  | 7 => pick5 i 73 42 156 5 38
  | 11 => pick5 i 5 50 44 73 42
  | 13 => pick5 i 50 49 38 5 41
  | 14 => pick5 i 49 50 5 38 41
  | 19 => pick5 i 44 5 38 156 49
  | 21 | 69 | 133 => pick5 i 42 41 38 5 210
  | 22 => pick5 i 41 42 5 38 49
  | 25 | 137 => pick5 i 38 5 42 41 150
  | 26 | 138 => pick5 i 5 38 41 42 150
  | 28 => pick5 i 5 41 44 210 150
  | 35 => pick5 i 156 5 150 44 41
  | 37 => pick5 i 210 73 150 5 42
  | 38 => pick5 i 73 210 5 150 41
  | 41 => pick5 i 150 5 156 73 38
  | 42 => pick5 i 5 150 73 49 38
  | 44 => pick5 i 81 5 73 156 49
  | 49 => pick5 i 5 150 81 38 41
  | 50 => pick5 i 5 81 150 41 38
  | 52 => pick5 i 73 5 81 150 41
  | 56 => pick5 i 5 73 150 156 38
  | 67 => pick5 i 44 5 38 73 210
  | 70 => pick5 i 41 42 5 38 73
  | 73 => pick5 i 38 5 42 41 210
  | 74 => pick5 i 5 38 41 42 81
  | 76 => pick5 i 49 5 41 44 81
  | 81 => pick5 i 38 5 50 49 73
  | 82 => pick5 i 5 38 49 50 73
  | 84 => pick5 i 41 5 49 150 73
  | 88 => pick5 i 5 41 150 156 73
  | 97 => pick5 i 150 5 38 41 210
  | 98 => pick5 i 5 150 41 38 210
  | 104 => pick5 i 5 156 38 41 81
  | 112 => pick5 i 5 150 38 49 73
  | 131 => pick5 i 44 5 38 156 150
  | 134 => pick5 i 41 42 5 38 210
  | 140 => pick5 i 49 5 41 44 210
  | 145 => pick5 i 38 5 50 49 150
  | 146 => pick5 i 5 38 49 50 156
  | 148 => pick5 i 41 5 49 210 150
  | 152 => pick5 i 5 44 49 150 156
  | 162 => pick5 i 5 41 38 156 150
  | 164 => pick5 i 73 5 41 38 210
  | 168 => pick5 i 5 73 38 41 150
  | 176 => pick5 i 5 81 38 49 210
  | 193 => pick5 i 38 5 73 150 210
  | 194 => pick5 i 5 38 73 156 150
  | 196 => pick5 i 41 5 73 156 210
  | 200 => pick5 i 5 41 81 73 150
  | 208 => pick5 i 5 49 73 81 150
  | 224 => pick5 i 5 38 73 150 210
  | _ => 0

def hardTriple (m : Cut) : Prop := terminals m = 3 ∧ m ≠ 100 ∧ m ≠ 161
instance (m : Cut) : Decidable (hardTriple m) := inferInstanceAs
  (Decidable (terminals m = 3 ∧ m ≠ 100 ∧ m ≠ 161))

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem pair_ones : ∀ m : Cut, terminals m = 2 → ∀ i : Fin 3,
    verdict (pairWitness m i) = true := by decide

theorem pair_crosses : ∀ m : Cut, terminals m = 2 → ∀ i j : Fin 3, i ≠ j →
    ¬ (verdict (mix (cutWord m) (pairWitness m i) (pairWitness m j)) = true ∧
       verdict (mix (cutWord m) (pairWitness m j) (pairWitness m i)) = true) := by decide

theorem triple_ones : ∀ m : Cut, hardTriple m → ∀ i : Fin 5,
    verdict (tripleWitness m i) = true := by decide

theorem triple_crosses : ∀ m : Cut, hardTriple m → ∀ i j : Fin 5, i ≠ j →
    ¬ (verdict (mix (cutWord m) (tripleWitness m i) (tripleWitness m j)) = true ∧
       verdict (mix (cutWord m) (tripleWitness m j) (tripleWitness m i)) = true) := by decide

/-- The only two exceptional triples share exactly terminal number five,
    using zero-based indices. -/
theorem exceptional_overlap :
    ((100 : Word) &&& 161 = 32) ∧ terminals 100 = 3 ∧ terminals 161 = 3 ∧ terminals 32 = 1 := by
  decide

def Covers {K : Type} (m : Word) (left right : K → Word → Prop) : Prop :=
  ∀ x, verdict x = true ↔ ∃ k, left k (row m x) ∧ right k (col m x)

theorem fooling_excludes {I K : Type} (m : Word) (witness : I → Word)
    (collision : ∀ color : I → K, ∃ i j, i ≠ j ∧ color i = color j)
    (ones : ∀ i, verdict (witness i) = true)
    (crosses : ∀ i j, i ≠ j →
      ¬ (verdict (mix m (witness i) (witness j)) = true ∧
         verdict (mix m (witness j) (witness i)) = true))
    (left right : K → Word → Prop) : ¬ Covers m left right := by
  intro cover
  have existsColor (i : I) := (cover _).mp (ones i)
  let color (i : I) := Classical.choose (existsColor i)
  have chosen (i : I) : left (color i) (row m (witness i)) ∧
      right (color i) (col m (witness i)) := Classical.choose_spec (existsColor i)
  obtain ⟨i,j,ne,eq⟩ := collision color
  have hi := chosen i
  have hj := chosen j
  rw [← eq] at hj
  apply crosses i j ne
  constructor
  · apply (cover _).mpr
    obtain ⟨r,c⟩ := mix_projections m (witness i) (witness j)
    exact ⟨color i, r ▸ hi.1, c ▸ hj.2⟩
  · apply (cover _).mpr
    obtain ⟨r,c⟩ := mix_projections m (witness j) (witness i)
    exact ⟨color i, r ▸ hj.1, c ▸ hi.2⟩

theorem no_two_rectangles (m : Cut) (two : terminals m = 2)
    (left right : Bool → Word → Prop) : ¬ Covers (cutWord m) left right :=
  fooling_excludes (cutWord m) (pairWitness m) NestedClauseCycle.repeatedColor
    (pair_ones m two) (pair_crosses m two) left right

theorem no_four_rectangles (m : Cut) (hard : hardTriple m)
    (left right : Fin 4 → Word → Prop) : ¬ Covers (cutWord m) left right :=
  fooling_excludes (cutWord m) (tripleWitness m) NestedClauseCycle.repeatedFourColors
    (triple_ones m hard) (triple_crosses m hard) left right

/-- The exceptional masks themselves have cover number exactly four. -/
def exceptionWitness (m : Cut) (i : Fin 4) : Word :=
  if m = 100 then
    if i = 0 then 5 else if i = 1 then 42 else if i = 2 then 38 else 73
  else
    if i = 0 then 5 else if i = 1 then 38 else if i = 2 then 41 else 150

def representative (m : Cut) (k : Fin 4) : Word :=
  if m = 100 then
    if k = 0 then 4 else if k = 1 then 32 else if k = 2 then 36 else 64
  else
    if k = 0 then 1 else if k = 1 then 32 else if k = 2 then 33 else 128

def rowType (m : Cut) (k : Fin 4) (x : Word) : Prop :=
  x = representative m k ∨
    (k.val < 3 ∧ x = (representative m k ||| (if m = 100 then 64 else 128)))

instance (m : Cut) (k : Fin 4) (x : Word) : Decidable (rowType m k x) := by
  unfold rowType
  infer_instance

def colType (m : Cut) (k : Fin 4) (y : Word) : Prop := verdict (representative m k ||| y) = true

instance (m : Cut) (k : Fin 4) (y : Word) : Decidable (colType m k y) := by
  unfold colType
  infer_instance

private instance existsFour (p : Fin 4 → Prop) [DecidablePred p] : Decidable (∃ k, p k) :=
  decidable_of_iff (p 0 ∨ p 1 ∨ p 2 ∨ p 3) (by
    constructor
    · rintro (h|h|h|h)
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
      · exact ⟨3,h⟩
    · rintro ⟨k,h⟩
      have casesK : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases casesK with rfl|rfl|rfl|rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))

theorem exceptional_four_cover (m : Cut) (cut : m = 100 ∨ m = 161) :
    Covers (cutWord m) (rowType m) (colType m) := by
  rcases cut with rfl | rfl <;> intro ⟨x⟩ <;> revert x <;> decide

private theorem repeatedThreeColors (f : Fin 4 → Fin 3) :
    ∃ i j : Fin 4, i ≠ j ∧ f i = f j := by
  have casesThree : ∀ a b c d : Fin 3, a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by decide
  rcases casesThree (f 0) (f 1) (f 2) (f 3) with h|h|h|h|h|h
  · exact ⟨0,1,by decide,h⟩
  · exact ⟨0,2,by decide,h⟩
  · exact ⟨0,3,by decide,h⟩
  · exact ⟨1,2,by decide,h⟩
  · exact ⟨1,3,by decide,h⟩
  · exact ⟨2,3,by decide,h⟩

theorem exceptional_no_three (m : Cut) (cut : m = 100 ∨ m = 161)
    (left right : Fin 3 → Word → Prop) : ¬ Covers (cutWord m) left right := by
  apply fooling_excludes (cutWord m) (exceptionWitness m) repeatedThreeColors
  · rcases cut with rfl | rfl <;> decide
  · rcases cut with rfl | rfl <;> decide

theorem disjoint_triples_cannot_both_have_four
    (m n : Cut) (threeM : terminals m = 3) (threeN : terminals n = 3)
    (disjoint : (cutWord m &&& cutWord n) = 0)
    (leftM rightM leftN rightN : Fin 4 → Word → Prop)
    (coversM : Covers (cutWord m) leftM rightM)
    (coversN : Covers (cutWord n) leftN rightN) : False := by
  have exceptional (k : Cut) (three : terminals k = 3)
      (a b : Fin 4 → Word → Prop) (c : Covers (cutWord k) a b) : k = 100 ∨ k = 161 := by
    by_cases first : k = 100
    · exact Or.inl first
    by_cases second : k = 161
    · exact Or.inr second
    exact False.elim ((no_four_rectangles k ⟨three, first, second⟩ a b) c)
  rcases exceptional m threeM leftM rightM coversM with rfl | rfl <;>
    rcases exceptional n threeN leftN rightN coversN with rfl | rfl <;>
    exact (by decide : ¬ _) disjoint

/-- Each four-terminal factor is a tree. Its two input pairs are read once. -/
def pairedClauses (a b c d : Bool) : Bool := (a || b) || (c && d)

def fourFactorVerdict (x : Word) : Bool :=
  let bit := x.getLsbD
  pairedClauses (bit 0) (bit 1) (bit 2) (bit 3) &&
  (bit 2 || bit 3 || bit 4) &&
  pairedClauses (bit 0) (bit 5) (bit 4) (bit 7) &&
  (bit 2 || bit 5 || bit 6)

/-- The first and second clauses share the pair 1,2. The fourth and sixth
    share 1,6. The four resulting scopes have fourteen incidences. -/
theorem four_factor_verdict (x : Word) : verdict x = fourFactorVerdict x := by
  decide +revert

#print axioms four_factor_verdict
#print axioms disjoint_triples_cannot_both_have_four
#print axioms exceptional_four_cover
#print axioms exceptional_no_three
#print axioms no_two_rectangles
#print axioms no_four_rectangles
#print axioms exceptional_overlap

end EightTerminalCycle
